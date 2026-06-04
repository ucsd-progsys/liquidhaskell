# REPORT: Relaxing the RApp Invariant for Trivial RProps

## Issue

[#2692](https://github.com/ucsd-progsys/liquidhaskell/issues/2692) — "splitc unexpected" panic
when constraint generation encounters structural mismatches involving `RProp _ (RHole _)`.

## Background: The RApp Invariant

The `RApp` constructor carries `rt_pargs :: [RTProp]` — abstract refinement
arguments. The invariant (documented in `RType.hs:869-888`) requires these to be
fully expanded (body matching the PVar type). However, `RProp bs (RHole r)`
appears legitimately in several situations:

1. During deserialization before `addTyConInfo` fills in defaults
2. In partially-applied type constructors
3. As initial placeholders from `rPropP`

Previously, encountering `RProp _ (RHole _)` at various processing stages would
trigger panics, even though the `mapBotRef` function (RTypeOp.hs:818) already
treats it as a terminal node that stops recursion.

## Implementation

The invariant is relaxed: `RProp bs (RHole trueReft)` (a "trivial RProp") is now
a valid, first-class representation meaning "this abstract refinement position is
unconstrained." The implementation touches 5 files:

### 1. `RefType.hs` — `mkRTProp` preserves trivial RHoles

When `mkRTProp` encounters `RProp ss (RHole r)` with `isTauto r`, it leaves it
in place rather than expanding to the full PVar type. This handles partial
applications and self-referential types where expansion is unnecessary or harmful.

```haskell
mkRTProp _pv (RProp ss (RHole r))
  | isTauto r = RProp ss (RHole r)
```

Note: `rtPropTop` still produces full types (`ofRSort (pvType pv)`) for defaults.
This is essential for abstract refinement verification, where the full type body
is freshened with KVars during constraint generation.

### 2. `Split.hs` — `rsplitC` and `rsplitW` handle trivial RHoles

Instead of panicking, these functions return `[]` (no constraints) when
encountering a trivial RProp:

```haskell
rsplitC _ _ (RProp _ (RHole r)) | isTauto r = return []
rsplitC _ (RProp _ (RHole r)) _ | isTauto r = return []
rsplitW _ (RProp _ (RHole _)) = return []
```

### 3. `Fresh.hs` — `trueRef` and `refreshRef` preserve trivial RHoles

These functions return trivial RHoles unchanged instead of panicking:

```haskell
trueRef _ (RProp s (RHole r)) = return $ RProp s (RHole r)
refreshRef _ (RProp s (RHole r)) = return $ RProp s (RHole r)
```

### 4. `PredType.hs` — Predicate substitution handles trivial RHoles

- `replacePreds`: skips substitution (identity) for trivial RProps
- `substPredP`: returns trivial RProp unchanged
- `meetListWithPSubRef`: returns the non-trivial operand when one side is trivial

### 5. `RTypeOp.hs` — `Top` instance for `RTypeBV`

The `top` function now produces `RHole (top r)` instead of panicking on `RHole`.

## Design Decision: Why Not Make `rtPropTop` Return `RHole trueReft`?

An initial approach made `rtPropTop` unconditionally return `RProp (pvArgs pv) (RHole trueReft)`.
This broke all abstract refinement tests (Map.hs, Maybe.hs, etc.) because:

1. Default RProps created by `rtPropTop` are freshened with KVars during constraint generation
2. These KVars participate in constraint solving for abstract refinement verification
3. Trivial defaults generate no KVars → no constraints → unsound results

The correct approach preserves the full type in defaults but allows trivial RHoles
to flow through the system gracefully when they arise from other sources (partial
applications, user-specified trivial predicates, etc.).

## Key Insight

The relaxation is NOT about changing what `addTyConInfo` produces — it's about
making the rest of the system robust to `RProp _ (RHole _)` appearing at any
stage. The `mapBotRef` function already treated them as terminal; now the
constraint generation, freshening, and predicate substitution layers do too.
