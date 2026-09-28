# Conventions

## Comments

A comment earns its place only by saying something that is neither in the code
nor recoverable from git. In practice that means warnings against plausible
wrong refactors, and non-obvious invariants.

Do not write a comment that restates what the code says. `/-- A universal
morphism from `X` to `G` -/` above `UniversalMorphism X G` carries nothing; the
signature already says it.

Do not put code history in a comment. That is what git is for. Rationale,
alternatives that were tried, and what changed belong in the commit message,
which can be as long as it needs to be.

Two examples that do earn their place:

```lean
/-! Not `commaCat (delta one X) G`: spelling `X` as a functor out of `one` leaves
    `one`'s two universe levels unconstrained, so they survive as junk parameters
    and trip `checkUnivs`. -/
```

The code records what was built, never what was rejected — without this someone
deletes `UnderOb` and reuses `commaCat`.

```lean
/-! `underCat`/`overCat` are plain `def`s, so `simp` cannot see through them at
    reducible transparency: a lemma stated over `UnderOb` rather than
    `(underCat X G).Ob` is silently never tried. -/
```

Without this the bridge lemmas read as deletable tautologies.


## Naming

| Kind | Convention | Examples |
|------|-----------|---------|
| Inductive types, structures | `PascalCase` | `Cat`, `Fun`, `ConeOb`, `NaturalTransformation` |
| Type formers — defs returning a `Sort` | `PascalCase` | `Lim`, `CoLim`, `Equalizer`, `Pullback` |
| Terms, including categories and functors | `camelCase` | `sortCat`, `two`, `equalizerDiagram`, `coneCat`, `categoryCat` |
| Theorem names | `snake_case` | `split_mono_to_mono`, `sortCat.mono_to_injective` |
| A named construction has a property | `<name>.is_<property>` | `natCat.is_mono`, `yonedaEmbedding.is_full` |
| Smart constructors | `<Type>.mk` | `Equalizer.mk` |

The line that needs care is between a *type former* and a *term*: `Lim F` is a
`Sort` you inhabit, so it is `PascalCase`, while `coneCat F` is a term of type
`Cat`, so it is `camelCase`. Both read as "produces something category-shaped",
but only the first is a type. By the same rule, the proof that a particular
category has a limit is a term: `sortCat.lim`, not `sortCat.Lim`.

An implication is named for its direction, `<from>_to_<to>`, hence
`split_mono_to_mono` rather than `split_mono_is_mono`.


## Namespaces

Two different things are being named, and only one of them buys syntax.

**Namespace is a type.** `Fun.ext`, `ConeOb.comm`, `TerminalObject.ext`,
`Equalizer.mk`. These give dot notation — `F.onHom`, `X.π`, `g.fac`, `E.T` —
which is the main reason to reach for a namespace at all.

**Namespace is a term.** `sortCat.equalizer`, `natCat.pullback`, `propCat.lim`,
`equalizerDiagram.A`. These give grouping only: `sortCat` is a value rather than
a type, so `x.equalizer` can never resolve. Still worth doing, since everything
known about a given category then shares one prefix.

Dot notation fires on the first *explicit* argument of the namespace's type. If
such an argument is made implicit the notation silently stops working, with no
warning, so prefer keeping it explicit and first.


## Building

`lake build`. The project has no dependencies, so a clean build is seconds and
needs no cache. Keep it that way: adding a `require` to `lakefile.lean` trades
a 27-job build for a multi-thousand-job one.

`#print axioms <name>` is the check that matters after touching anything in
`Instances/`. `Classical.choice` should appear only where choice is genuinely
being used; everything else stays constructive.


## Module structure

```
Primus/
  Core/       Base structures: Cat, Fun, NatTrans, Opposite, Product, Comma, Delta
  Diagrams/   Diagram shapes: ordinals (Zero–Four), Discrete, Nat,
              EqualizerDiagram, PullbackDiagram
  Limits/     Cone, CoCone, Lim, CoLim
  Instances/  Concrete categories: SortCat, PropCat
  Yoneda/     Hom functor and Yoneda lemma
```

## Diagram shapes

The ordinal categories are the representable objects of the simplex category Δ:

| File | Category | Purpose |
|------|----------|---------|
| `Zero` | ∅ | empty category |
| `One` | [0] | single object; terminal in `Cat` |
| `Two` | [1] | walking morphism |
| `Three` | [2] | walking composable pair (composition) |
| `Four` | [3] | walking composable triple (associativity) |
