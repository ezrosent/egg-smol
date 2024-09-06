# An Experimental Backend for Egglog

This crate contains utilities that could serve as a "backend" for the egglog
language. As the language grows and acquires more features, it may be a good
idea to split out core functionality into separate crates. This crate implements
core database and query primitives, other crates could implement: syntax,
type-checking, extraction, etc.  There are two main crates here,
`core-relations` and `egglog-bridge`, with the other crates being much smaller.
`core-relations` provides the lowest-level primitives, while `egglog-bridge`
exposes a "middle-end" layer without much type-checking, but with higher-level
features like proofs and seminaive evaluation.


## `core-relations`

The `core-relations` crate is the main "backend" portion of the code: it defines
relations and implements relational algebra-style queries against those
relations. 

### Extensible Tables

Relations are exposed behind an API: we implement this API for
standard egglog-style timestamp-sorted hash tables as well as various forms of
union-find backed tables. The table abstraction used in this crate is also a bit
more expressive than egglog: tables can have multiple non-primary keys, for
example. The structure here is influenced by the
[BYODS paper](https://dl.acm.org/doi/10.1145/3622840).

### Free Join

Instead of GJ, this repo implements the [Free Join](https://arxiv.org/abs/2301.10841)
algorithm. Free Join combines many of the theoretical benefits of GJ with the
practical benefits of an execution model closer to standard hash joins,
including vectorized execution. The implementation in this crate differs from
the paper somewhat: 

* We do not start with a left-deep hash join plan, we instead create a Free Join
plan from scratch, relying on a similar heuristic to the one employed in egglog:
intersect with smaller relations earlier in the join plan. Unlike egglog, the
Free Join planner also tries to minimize the number of stages in the final join
plan; this concept only makes sense with Free Join as all GJ plans have as many
stages as there are variables in the query.

* We do not use a lazy trie. Instead, we keep trie levels in a common cache of
hash tables, allowing for more memory reuse across different recursive calls
to Free Join.

### Lower-level Control

The `Db` API in this crate allows for arbitrary subsets of rules to be run.
Callers can pass a callback that allows them to access the raw results of a
query so as to read arbitrary values out of the database.

Rebuilding is also *optional*. While strange things may happen if rebuilding is
only called sometimes, there is virtually no overhead for queries written
without congruence in mind. Egglog-style congruence closure can be opted into
via manual calls to `union` and `rebuild`.

### Pluggable Primitives

This crate exports an API for adding arbitrary primitive types (and arbitrary
operations on them) into the database.

### ... And More

Much of the rest of the crate follows egglog's current structure, though with
subtle differences.

* The APIs for Tables and Indexes have been reworked to centralize the
  responsibility of invariant maintenance in a single module.
* There are separate numeric Id types for each different kind of numeric index.
* String interning is optional and thread-local, eliminating the only source of
  nondeterminism in egglog, at the cost of some debugability.

### What isn't done

There is a lot more to do here at the level of this crate. The big areas where
things can improve are:

* Support for parallelism: like egglog, `core-relations` is currently single-threaded.
* Better query optimizations: e.g. dynamic variable ordering, support for bushy plans.

## `egglog-bridge`

The `egglog-bridge` crate implements a small egglog-like language as a Rust
library on top of `core-relations`. It exposes a builder-pattern-style API, as
well as a macro that supports S-expression syntax.  It is currently missing
support for lattices and containers. But it has initial support for proofs.