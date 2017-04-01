# Raft spec in PlusCal

This doc describes a specification of the [Raft][raft-website] distributed consensus algorithm
using PlusCal. The author of Raft, Diego Ongaro, has already written a [TLA+ spec
of Raft][raft-tla-spec], but I wanted to write in PlusCal in order to better learn
PlusCal and to see if I could write a more readable spec than the original,
which I find difficult to follow.

[raft-website]: https://raft.github.io/
[raft-tla-spec]: https://github.com/ongardie/raft.tla

## Overview

Functionally, Raft implements a key-value data store. If we were to define its
interface in Java, it would look something like this:

```java
interface Store {
    void Write(String key, int value);

    int Read(String key);
}
```

(For simplicity, I've assumed the store only supports integers).



More specifically, Raft claims to implement a
[linearizable][bailis-linearizability] store.

[bailis-linearizability]: http://www.bailis.org/blog/linearizability-versus-serializability/
