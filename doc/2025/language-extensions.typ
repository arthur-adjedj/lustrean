= Extending `Lustrean`

== New primitives

`pre`, →, `fby`
// explain semantics

== Rejecting ill-formed programs

Examples

```lustre
node f(x) = x where
```

```lustre
node f(x,x) = y where
```

```lustre
node f(x) = y,y where
```
→ here we can redefine `z = y` in the body

== Type checking

- pour l'instant, `int` and `bool`, avec une possibilité d'étendre le TS facilement
- opérations arithmétiques → type check pour avoir des `int` (statiquement)
- opérations booléennes → type check pour avoir des `bool`
- comparaisons → type check pour avoir les mêmes types

=== Design choices

`int` are really implemented as singleton intervals in the reify phase (during elaboration)
