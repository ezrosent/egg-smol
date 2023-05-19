# An Experimental Backend for Egglog

This crate contains utilities that could serve as a "backend" for the egglog
language. As the language grows and acquires more features, it may be a good
idea to split out core functionality into separate crates. This crate implements
core database and query primitives, other crates could implement: syntax,
type-checking, extraction, etc. 

In addition to factoring some utilities out, this crate explores the following
techniques:

## Free Join

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

## Lower-level Control

The `Db` API in this crate allows for arbitrary subsets of rules to be run.
Callers can pass a callback that allows them to access the raw results of a
query so as to read arbitrary values out of the database.

Rebuilding is also *optional*. While strange things may happen if rebuilding is
only called sometimes, there is virtually no overhead for queries written
without congruence in mind. Egglog-style congruence closure can be opted into
via manual calls to `union` and `rebuild`.

## Pluggable Primitives

This crate exports an API for adding arbitrary primitive types (and arbitrary
operations on them) into the database.

## ... And More

Much of the rest of the crate follows egglog's current structure, though with
subtle differences.

* The APIs for Tables and Indexes have been reworked to centralize the
  responsibility of invariant maintenance in a single module.
* There are separate numeric Id types for each different kind of numeric index.
* String interning is optional and thread-local, eliminating the only source of
  nondeterminism in egglog, at the cost of some debugability.
