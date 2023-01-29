# RFC: Custom Handling for Associative and Commutative Functions


## Summary

Introduce new syntax to egglog allowing binary operators to be declared as associative and commutative:

```
(data Expr
    (Num i64)
    (Add Expr Expr :assoc_comm)
```

This would replace rewrites expressing associativity and commutativity of `Add`:

```
(rewrite (Add a b) (Add b a))
(rewrite (Add a (Add b c)) (Add (Add a b) c))
```

The `:assoc_comm` flag would behave equivalently[^1] to a datatype with the above rewrites, but it uses a more compact representation for iterated applications of commutative operators. 

This document covers motivation for this feature and a sketch of how it could be implemented.

## Motivation

It is fairly common to model commutative semigroups in egglog. Commutative and associative operations are common in program analysis and equality saturation, and axioms conveying associativity and commutativity are common in egglog and egg programs.

One downside of expressing commutativity and associativity as rewrite rules in egglog is exponential growth: For $n$ iterated applications of a commutative and associative operation $(a_1 + a_2 + \ldots + a_n)$, egglog will attempt to compute $n!$ permutations of these operators along with all possible associations of _each_ permutation (of which the number is [something like $(n-2)!!$](https://cs.stackexchange.com/questions/112694/algorithm-for-the-complete-parenthesization-of-n-factors)).

While egglog uses hashconsing and structural sharing to reduce the overall size in memory, it still has to explicitly compute the tops of each of these syntax trees separately at least once. This is a problem in practice: it's very common to see associativity rules be banned by a backoff scheduler because they match too many nodes, but that means that only a subset of permutations can be matched by the remaining rules in the egglog program.

Intuitively, an associative and commutative operation like addition can be represented as a [nonempty multiset](https://en.wikipedia.org/wiki/Free_monoid#The_free_commutative_monoid) of distinct terms participating in an iterated application of the operation. This proposal sketches how to transparently implement `:assoc_comm` nodes in egglog using a persistent multiset datastructure, in addition to some indexing tricks to allow it to play nicely with existing egglog semantics.

## Implementation Sketch

The high-level proposal is to introduce a new function $F^*$ for each `:assoc_comm` function $F$. $F$ must be a binary function with the same sort for its output and all inputs. $F^*$ will map a multiset of elements of this sort to the output. We'll use `Add` and `Add*` to follow the running example. Intuitively, nodes like:

```
    (Add a (Add b c))
    (Add (Add a  b) c)
    (Add (Add b  a) c)
    ...
```

Will all be replaced internally by a single node:

```
    (Add* a b c)
```

To get this to work, we need to:
* Translate queries involving `Add` into equivalent queries over `Add*`.
* Explain how to canonicalize `Add` nodes introduced by rules back into `Add*` nodes.

First, we'll examine the internal representation of functions like `Add*`.

### Multiset Function representation

Multiset functions over a sort $S$ will map a single multiset to an output id in $S$. As we will see, we may have to insert copies of a given multiset with a small number of changes into the table. As such, we'll want

* A persistent / functional datastructure for the underlying map or set.
* Support for efficient hashing, either using a commutative hash combiner[^2] or via a data-structure with a unique canonical representation (HAMTs may be sufficient here). Storing a hash value along with the set will allow for efficient deduping.

Standard persistent hash maps or tries from keys to integers (i.e. multiplicities) should get us off the ground here, though some of the points around rebuilding below indicate we could benefit from a custom implementation.

With such a data-structure in place, the existing egglog concepts carry over in a more or less natural way:

#### Indexes

#### Efficient rebuilding


### Flattening Rules

### Merge Handling

### GJ Integration

## Alternatives

### Hold out for something more general
(What about _just associative_)
(What about _S_ rule)

### Infer commutativity in rewrites
(TODO: explicit is better)


[^1]: Up to the number you pass to `run`, i.e. the same rules will fire with `:assoc_comm` as with the usual rewrites, but they may not fire at the exact same iteration.

[^2]: See [Hashing Modulo Alpha-Equivalence](https://simon.peytonjones.org/assets/pdfs/hashing-modulo-alpha.pdf) for an example, but also keep [some caveats](https://pvk.ca/Blog/2022/12/29/fixing-hashing-modulo-alpha-equivalence/) in mind about collision rates from that paper.