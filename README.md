# Raft spec in PlusCal

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
[PlusCal]: http://lamport.azurewebsites.net/tla/pluscal.htm

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

## Linearizability

Raft claims to implement a [linearizable][bailis-linearizability] store. From
[Herlihy and Wing][herlihy-linearizability], who introduced linearizability:

> Linearizability provides the illusion that each operation applied by
> concurrent processes takes effect instantaneously at some point between its
> invocation and its response...
> ...
> First, each operation should appear to “take effect” instantaneously, and
> second, the order of nonconcurrent operations should be preserved.



[bailis-linearizability]: http://www.bailis.org/blog/linearizability-versus-serializability/
[herlihy-linearizability]: http://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf
