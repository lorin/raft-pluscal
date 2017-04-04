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
