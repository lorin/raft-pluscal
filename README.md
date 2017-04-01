# Raft spec in PlusCal

## Introduction

This doc describes a specification of the [Raft][raft-website] distributed consensus algorithm
using PlusCal. The author of Raft, Diego Ongaro, has already written a [TLA+ spec
of Raft][raft-tla-spec], but I wanted to write in PlusCal in order to better learn
PlusCal and to see if I could write a more readable spec than the original,
which I find difficult to follow.

[raft-website]: https://raft.github.io/
[raft-tla-spec]: https://github.com/ongardie/raft.tla

## Functional interface

Functionally, Raft implements a key-value data store. If we were to define its
interface in Java, and we assume for simplicifity that it only supports
integers, it would look something like this:

```java
interface Store {
    void Write(String key, int value);

    int Read(String key);
}
```

Since this is a distributed system, we need to think in terms of messages: a
client sends a write or a read request to the store, and the store eventually
replies with a response.

I'm going to model the behavior of the store using the following four actions:

* WriteRequest - store receives a write request message
* WriteResponse - store sends a write response message
* ReadRequest - store receives a read request message
* ReadResponse - store sends a read response message

The user issues a WriteRequest, passing a key and a value (e.g., "x=8"). After
the server succeeds, it responds.





## Linearizability

Raft claims to implement a [linearizable][bailis-linearizability] store.

[bailis-linearizability]: http://www.bailis.org/blog/linearizability-versus-serializability/
