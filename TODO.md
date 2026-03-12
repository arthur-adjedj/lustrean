<!-- LTeX: language=fr-FR -->

# TODO

## Léo

- [x] rejeter les programmes mal formés (eg `node f(x,x) = x,x where x = 1; x = 2`)
  - [x] pas d'overlap entre entrée/sortie
  - [x] pas de doublon dans l'entrée + la sortie
  - [x] pas de double binding dans le corps
- [ ] étendre l'AST, e.g pour rajouter `pre`, `->`, des expressions booléennes
- [ ] rajouter du typage (bool, int, string; `Syntax -> Expr` becomes `Syntax -> Σ(T:Typ): Expr T`), y compris potentiellement du typage de clock (en simplifiant les comparaisons au début)
- [ ] potentiellement ne pas checker les clocks au typage mais plus tard avec les domaines, ça permettrait d'accepter + de programmes potentiellement

## Fernando

- [ ] rajouter des domaines plus fins pour vérifier les `guard` et les `undefined`, e.g
  - [ ] domaines relationels linéaires
  - [ ] domaines relationels octogonaux
  - [ ] domaines non-relationels avec unions d'intervalles (avec nombre d'intervalles dans l'union borné)
  - [ ] domaine conditionnel (partition de l'espace avec des prédicats e.g pour split sur les if-then-else, et potentiellement split sur les ticks pour simplifier des exprs)

## Arthur

- [ ] rajouter un interpréteur qui traduit l'AST vers des itérators, et potentiellement la vérifier (vérification lourde, implique de prouver que l'interpréteur abstrait surinterprète la sémantique de l'interprétateur concret)
- [ ] packager le système d'interp abstrait dans une tactique pour prouver la soundness de nos programmes de manière modulaire
