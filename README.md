# Raft spec in PlusCal

## Introduction

This doc describes a specification of the [Raft][raft-website] distributed consensus algorithm
using PlusCal. The author of Raft, Diego Ongaro, has already written a [TLA+ spec
of Raft][raft-tla-spec], but I wanted to write in PlusCal in order to better learn
PlusCal and to see if I could write a more readable spec than the original,
which I find difficult to follow.

I'm going to draw heavily on the memory interface examples from Leslie Lamport's
[Specifying systems][book] book, so you'll see similarities in some of the specs
here to those examples.

[raft-website]: https://raft.github.io/
[raft-tla-spec]: https://github.com/ongardie/raft.tla
[book]: http://lamport.azurewebsites.net/tla/book.html

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

I'm going to model the behavior of the store using the following four actions:

* WriteReq - store receives a write request message
* WriteResp - store sends a write response message
* ReadReq - store receives a read request message
* ReadResp - store sends a read response message

The user issues a WriteRequest, passing a key and a value (e.g., "x=8"). After
the server succeeds, it responds.

I need to express this initial interface in TLA+, not PlusCal, since PlusCal is
for expressing algorithms, and here I'm just specifying an interface.

TLA+ models behaviors as state variables that change over time.

(Note: this model is quite similar to Section 5.1 of [Specifying Systems][book]).

For this functional specification, I'm going to use a single state
variable called `store` that represents the entire state of our data store.

```
VARIABLE store
```

In a typical TLA+ model, you define actions which describes how state
variables are permitted to change under the specification.

If we assume WriteReq, WriteResp, ReadReq and ReadResp were operators that
returned boolean values, we could use them to specify TLA+ actions. For example

(For each example, imagine the text is preceded wtih, "The operator will return
true when the system ...")

receives a write request to set x=8:

```
WriteReq("x", 8, store, store')
```

sends a write response that x was set to 8:


```
WriteResp("x",8, store, store')
```

sends a read request to get the value of x:

```
ReadReq("x", store, store')
```

sends a read response that the value of "x" is 8.

```
ReadResp("x", 8, store, store')
```

In the specification, we describe that these are operators:

```
CONSTANTS   WriteReq(_, _, _, _),
            WriteResp(_, _),
            ReadReq(_, _),
            ReadResp(_, _, _),
```

We also want to define constants that represents the set of allowed variables
and values:

```
CONSTANTS   Variables, Values
```

We also need to specify the initial state that the store variable can be in. We
create a constant that represents the state of valid initial states for the
`store` variable.

```
CONSTANT    InitStore
```

Finally, we specify that the operators are boolean valued.

```
ASSUME \A var \in Variables, val \in Values, stOld, stNew :
        /\ WriteReq(var, val, stOld, stNew)  \in BOOLEAN
        /\ WriteResp(var, val, stOld, stNew) \in BOOLEAN
        /\ ReadReq(var, stOld, stNew)        \in BOOLEAN
        /\ ReadResp(var, val, stOld, stNew)  \in BOOLEAN
```


See [Store.tla](Store.tla) for the full module.

## Sequential store

Before we implement a specification for Raft, we'll start with something
simpler: a specification for a *sequential* store. By a sequential store, we
mean that the clients cannot make concurrent requests: only one client is
permitted to make a request at a time.

The specification will contain two kinds of processes:

* clients that submit read and write requests
* the store that processes the requests and responds



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
