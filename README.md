# Raft spec in PlusCal (work in progress)

## Introduction

This doc describes a specification of the [Raft][raft-website] distributed consensus algorithm
using [PlusCal]. The author of Raft, Diego Ongaro, has already written a [TLA+ spec
of Raft][raft-tla-spec], but I wanted to write in PlusCal in order to better learn
PlusCal and to see if I could write a more readable spec than the original,
which I find difficult to follow.

I'm going to draw heavily on the memory interface examples from Leslie Lamport's
[Specifying systems][book] book, so you'll see similarities in some of the specs
here to those examples.

[raft-website]: https://raft.github.io/
[raft-tla-spec]: https://github.com/ongardie/raft.tla
[book]: http://lamport.azurewebsites.net/tla/book.html
[PlusCal]: http://lamport.azurewebsites.net/tla/pluscal.html

## Functional interface

Let's start by specifying an interface that describes the functionality
that Raft provides. The specification at this level won't have anything about
the Raft implementation itself, it will apply equally to any other kind of
system that provides the same functional behavior (a non-distributed
implementation, a Paxos-based one, etc.).

Functionally, Raft implements a key-value data store. If we were to define its
interface in Java, and we assume for simplicifity that it only supports
integers, it would look something like this:

```java
interface Store {
    void Write(String key, int value);

    int Read(String key);
}
```

Since we're modeling a distributed system, we need to think in terms of messages: a
client sends a write or a read request to the store, and the store eventually
replies with a response.

## Sequential store

Before we implement a specification for Raft, we'll start with something
simpler: a specification for a *sequential* store. By a sequential store, we
mean that the clients cannot make concurrent requests: only one client is
permitted to make a request at a time.

The specification will contain two kinds of processes:

* clients that submit read and write requests
* the store that processes the requests and responds

Since only one client can make a request at a time in a sequential store, we
could use a single client as a model. Instead, I'm going to use multiple
clients, but use a mutex to ensure that only one client executes at a time. This
should make the code easier to generalize to the final Raft implementation.

My focus here is on readability of the model, so I'm going to make heavy use of
PlusCal macros so the model is easier to read.

The complete model is at [SequentialStore.tla](SequentialStore.tla), I'll
describe elements of it here.

Here's how the clients behave:

```
process Client \in 1..N
begin
c1: acquireMutex();
c2: with var \in Variables, val \in Values do
        either sendReadRequest(var);
        or sendWriteRequest(var, val)
        end either;
    end with;
c3: awaitResponse();
c4: releaseMutex();
    goto c1;
end process
```

A client acquires a mutex to ensure that client requests don't overlap. Clients
send or a request for a read or a write, and then wait for a response.

Here's the store behavior:

```
process Store = 0
variables request,
          response,
          dict = [x \in Variables |-> NoVal];
begin
s1: getNextRequest();
s2: if request.op = ReadOp then
        response := Message(ResponseType, request.client, ReadOp, request.var, dict[request.var]);
    else \* it's a write
        dict[request.var] := request.val;
        response := Message(ResponseType, request.client, WriteOp, request.var, request.val);
    end if;
s3: responseQueues[response.client] := Append(responseQueues[response.client], response);
s4: goto s1;
end process
```

The store retrieves the next request from its queue, and then either reads to
the `dict` variable if it's a read, or writes to it if it's a write. It takes
the response message and places it at the head of the queue corresponding to the
client.

The safety property we are interested in here is: every read of a variable must
correspond to the most recent write of that variable. I expressed that like
this:

```
ReadLastWrite == \A i \in 1..Len(log), var \in Variables, val \in Values :
   IsRead(i, var, val) =>
       \E j \in 1..(i-1) : /\ IsWrite(j, var, val)
                           /\ ~ \E k \in (j+1)..(i-1), v \in Values \ {val}: IsWrite(k, var, v)
```

In order to check this property, I needed to keep track of the history of
requests and responses. To do that, I created a variable called `log` that
contains a sequence. Every time a client sends a request or receives a response, the client appends
to the log:

```
macro sendRequest(msg) begin
    requestQueue := Append(requestQueue, msg);
    log := Append(log, msg);
end macro;

...

macro awaitResponse()
begin await Len(responseQueues[self]) > 0;
      log := Append(log, Head(responseQueues[self]));
      responseQueues[self] := Tail(responseQueues[self]);
end macro;
```

The `log` variable is a good example of a bookkeeping variable that would not
appear in a actual implementation, but is needed in the model in order to check
a property with the model checker.

### Checking liveness

As an exercise, we'll do a simple liveness check. The check we'll do is to
ensure that clients can always make progress.

Here's the liveness property we'll check:

```
AllClientsEventuallyRun == \A client \in 1..N : []<>(pc[client] = "c2")
```

This says that clients can always eventually reach label "c2".

This property isn't satisfied by this model: client 1 could keep reacquiring the
mutex, starving client 2. The TLA+ toolbox will check this for us.

Liveness checks require temporal properties, which are much slower to check in
the TLA+ toolbox than invariants.

Before I ran the liveness check, I commented out all code that involved the
"log" variable. That variable is only used for checking a safety property, and
without it the liveness check is much simpler.

I deliberately chose a small model to make things simple. These are the
variables specified by "What is the model" in the Model Overview of the TLA+
toolbox.

```
WriteOp <- "Write"
ReadOp <- "Read"
N <- 2
ResponseType <- "Response"
Variables <- [ model value ] {x}
defaultInitValue <- [ model value ]
Values <- {1}
NoVal <- [ model value ]
RequestType <- "Request"
```

The property we check is "AllClientsEventuallyRun".

This model runs in under a second. It immediately finds an error: "Temporal
properties were violated".

In the Error-Trace window on the right, the last line is `<Back to state 5>`.
The model checker found a path where it could loop forever without the liveness
proeprty being true.

## Linearizability

Raft claims to implement a [linearizable][bailis-linearizability] store. Before
we get into the Raft implementation itself, let's make it clear what
linearizability is.

From [Herlihy and Wing][herlihy-linearizability], who introduced linearizability:

> Linearizability provides the illusion that each operation applied by
> concurrent processes takes effect instantaneously at some point between its
> invocation and its response...
> ...
> First, each operation should appear to “take effect” instantaneously, and
> second, the order of nonconcurrent operations should be preserved.

More formally, from the Hierlihy and Wing paper:


A history H is *linearizable* if it can be extended (by appending zero or more
response events) to some history H' such that

**L1**: *complete(H')* is equivalent to some legal sequential history S, and

**L2**: `<_H \subseteq <_S`

where:

A *history* is a finite sequence of operation *invocation* and *response*
events. You can think of these events as being from a client's point of view: a
client invokes an operation on an object, and, some time in the future, the
client receives a response from the object.

*complete(H')* is the maximal subsequence of H consisting only of invocations
    and matching responses

`<_H` is an irreflexible partial order of operations in H in H:

`e0 <_H e1` if res(e0) precedes inv(e1) in H, where res(e0) is the response
associated with operation e0, and inv(e1) is the invocation of operation e1.

[bailis-linearizability]: http://www.bailis.org/blog/linearizability-versus-serializability/
[herlihy-linearizability]: http://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf
<img src="http://www.sciweavers.org/tex2img.php?eq=%3C_H%20%5Csubseteq%20%3C_S&bc=White&fc=Black&im=jpg&fs=12&ff=arev&edit=0" align="center" border="0" alt="<_H \subseteq <_S" width="65" height="17" ></_H>

## Raft


