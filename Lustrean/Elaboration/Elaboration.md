This project deals with a core language inspired by Lustre, a sort of
mini-lustre. The syntax of mini-lustre is given in
[Syntax.lean](Syntax.lean). Examples of mini-lustre programs can be found in the top level [Examples.lean](../../Example.lean) file. Here's a particular example.

```
node f(x) = o
guard
    x ≥ 0
where
    o = if x > 3 then 3 else x
assert
    0 ≤ x
    x ≤ 4
```

Compilation of mini-lustre have the following stages:

- [Reification](#reification)
- [Inlining](#inlining)
- [Indicisation](#indicisation)
- [Normalization](#normalization)
- [Compilation](#compilation)

## Reification

At the reification phase, the custom Lean `Syntax` used to write mini-lustre
programs is transformed into more specific structures. The purpose of this step
is to get out of the `CoreM` monad and allow us to work on simple Lean
datatypes.

## Inlining

As a simplification step, we replace all calls to other nodes in mini-lustre
code by their body

The following

```
node f(x) = o where
  o = x + 1
node g(x) = o where
  o = f(x) + 1
```

turns into

```
node g(x) = o where
  o = (x + 1) + 1
```

## Indicisation

The variables are replaced by indices, differentiating between input and bound
variables.

## Normalization

This phase introduces:

- implicit step variables (used to compile the `fby` construct)
- persistent state variables (used to compile the `pre` construct)
- subexpression variables (so any expressions that requires persistent state can be referenced from a variable)

- [ ] TODO: What are these?

## Compilation

It transfoms our normalized node representation into a Control flow graph. The
control flow graph is represented by

```lean
List (PreNode n) × Array (WithRef (Fin n))
```

where [PreNode](../Imp.lean) represents vertices in the node graph. The edges
can be found in the [PreNode.out_nodes](../Imp.lean) property, which give for
each vertex the list of vertices they are connected with, as well as the
instruction they carry.
