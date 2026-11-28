# Coinduction and Codata in LiquidHaskell

**Status:** Working design proposal

**Last modified:** 2026-11-28

## Goal and scope

Add sound support for potentially infinite data, productive corecursion, and coinductive proofs in LiquidHaskell. This addresses the difficulty of reflecting non-terminating generators such as `ones = Cons 1 ones` in a logic that assumes total definitions.

For v1, scope is **first-order algebraic codata** (such as streams and infinite trees) with direct recursion. Higher-order/negative codata and mutual coinduction are out of scope.

## Proposed annotations

```haskell
{-@ codata Stream a @-}
data Stream a = SCons a (Stream a)

{-@ reflect up @-}
up :: Int -> Stream Int
up n = SCons n (up (n + 1))

{-@ copredicate allPos @-}
allPos :: Stream Int -> Bool
allPos (SCons x xs) = x > 0 && allPos xs

type Proof = ()

{-@ colemma upPos :: n:{Int | n > 0} -> {allPos (up n)} @-}
upPos :: Int -> Proof
upPos n = upPos (n + 1)
```

- **`codata T`** targets a Haskell datatype (`TyCon`). In v1, its fields must be first-order algebraic: higher-order/negative fields such as `Input -> Stream` are excluded. A base constructor is not required; a codata type may still have one.
- **`copredicate P`** targets a reflected function returning `Bool`/`Prop` over codata. It marks a greatest-fixed-point (`ν`) property, such as stream bisimulation or an infinite-trace invariant. It is not a measure. The annotation is explicit: a function can accept codata and still be an ordinary terminating function, as with `take :: Nat -> Stream a -> [a]`, which terminates on `Nat`.
- **`colemma thm`** targets a proof function returning `Proof` (`()`), with a postcondition asserting a copredicate. Recursive proof calls are interpreted through finite-prefix induction rather than ordinary structural induction on codata.

Copredicate self-occurrences must be **positive** (monotone). For example, `&&` preserves positivity; negation and an occurrence on the left-hand side of an implication do not. Productivity checking applies to codata producers; copredicate checking concerns monotonicity, not constructor guardedness.

## Codata and recursive-call checking

A codata declaration identifies potentially infinite data and removes inductive grounding requirements that do not apply to it:

- A base/terminating constructor is not required.
- Inductive well-foundedness obligations such as generated decreasing `autolen` metrics do not apply to the codata type.
- Recursive calls guarded by a constructor of the codata type are checked for productivity rather than required to decrease an ordinary termination metric.

This must **not** disable termination checking for an entire function. Recursive calls are checked according to how they make progress:

- A recursive call beneath a codata constructor is guarded and can be justified by productivity.
- An unguarded recursive call must still satisfy ordinary termination checking.
- Mixed recursive/corecursive definitions must satisfy both checks on their respective calls.

`FivesUp` illustrates the mixed case. Calls that skip values until the next multiple of five are unguarded and decrease the metric `4 - ((n - 1) mod 5)`. Once a multiple of five is emitted under `SCons`, the recursive call is guarded. Both forms of progress must be checked.

Conversely, `filterStream` must be rejected: its `otherwise` branch recurses without producing a constructor, and it can skip forever on an input with no matching elements.

## Producers, consumers, and reflection

Productivity of a producer does not make every computation over its output terminating. A producer such as `ones = SCons 1 ones` can be valid because each recursive call is guarded. A consumer that traverses an arbitrary codata value can still diverge.

For example, `take :: Nat -> Stream a -> [a]` is an ordinary terminating function because it decreases its `Nat` argument. By contrast, consider a codata type with both `SEmpty` and `SCons`:

```haskell
slength SEmpty = 0
slength (SCons _ xs) = 1 + slength xs

ones = SCons 1 ones
```

`slength ones` does not terminate. Reflecting both definitions would allow a refinement such as `{slength ones == 0}` to contain a non-terminating computation. Codata support must not admit such a computation into LiquidHaskell's total logic; a consumer must be known to terminate over its reflected input domain.

## Coinduction through finite prefixes

The proposed proof mechanism reduces coinduction to ordinary induction on a finite depth `k`:

1. For each copredicate `P`, LiquidHaskell synthesizes an indexed prefix predicate `P_prefix s k` with termination metric `[k]`.
2. The prefix predicate is trivially true at `k = 0`; larger depths inspect one codata layer and recurse with a smaller `k`.
3. A `colemma` is desugared into an inductive helper proving `P_prefix s k` for every `k`.
4. The result is lifted to `P s` through the prefix bridge (Axiom D):

   `((forall k : Nat. P_prefix s k)) => P s`

This is the proposed route from finite observations to a coinductive property. For example, `upPos` should let users prove positivity of `up n` without manually defining indexed predicates or writing the bridge proof. Existing `TruePositives.hs` contains manual prefix proofs that illustrate this desugaring.

## PLE and corecursive generators

Non-terminating definitions are unsound in LiquidHaskell's total logic independently of PLE. PLE has a separate operational concern: unrestricted unfolding of a generator such as `ones = SCons 1 ones` can produce an infinite unfolding loop.

The proposed behavior is to withhold the bare recursive generator equation from PLE's unconditional unfolding set and expose constructor-field observations instead. For example, selector applications can reduce `hd ones` to `1` and `tl ones` to `ones`, revealing one constructor layer when demanded. General coinductive properties are handled through finite-prefix approximations.

This accounts for the difference between ordinary recursive definitions, whose case analysis can stop unfolding, and generators such as `ones`, whose definition has no case split to stop repeated unfolding.

## Example coverage

PR #2777 adds four groups of examples, all written in existing LiquidHaskell syntax. They establish current behavior against intended behavior; they do not yet exercise the proposed `codata`, `copredicate`, or `colemma` annotations.

| File | Cases | Current LH | Intended behavior |
| --- | ---: | --- | --- |
| `TruePositives.hs` | 10 | Accept | Accept |
| `TrueNegatives.hs` | 12 (+3 Dafny reference cases) | Reject | Reject |
| `FalsePositives.hs` | 7 | Accept | Reject |
| `FalseNegatives.hs` | 15 | Reject | Accept |

`TruePositives.hs` is especially relevant to the proposed proof mechanism: it defines indexed predicates such as `eqK`, proves properties by induction on `k`, and lifts them through bridge lemmas such as `approx`. Under the proposed annotations, examples such as `upPos` and `mapFusion` should express the same reasoning without this manual prefix boilerplate.

Representative intended rejections include:

- `filterStream`: an unguarded recursive call can skip output forever.
- `badCopredicate`: recursive occurrence under negation violates monotonicity.
- `falseStream`: an unguarded recursive proof claims `False`.
- `sink`, mutual unguarded recursion, and strict recursive fields: no productive constructor progress.

Representative intended acceptances include productive generators and coinductive proofs for `up`/`upPos`, `FivesUp`, stream mapping and fusion, merging/interleaving, bisimulation, and Moessner's construction.

The examples are a semantic baseline in existing LH syntax, and do not include the proposed ones yet. The next examples should include representative valid and invalid modules using the proposed annotations. In particular, invalid colemmas should show expected diagnostics. Those diagnostics should help users identify the mistake in their source proof even when the proof is desugared into generated helpers. Existing LiquidHaskell error-reporting conventions are the starting point; exact wording and implementation are not specified here.


The initial proposal keeps the coinductive proof principle in the LiquidHaskell frontend by reducing it to well-founded induction on `k`, rather than adding coinduction to SMT reasoning.
