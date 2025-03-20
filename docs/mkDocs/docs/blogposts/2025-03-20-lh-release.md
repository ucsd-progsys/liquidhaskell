---
layout: post
title: A hundred pull requests for Liquid Haskell
date: 2025-03-20
comments: true
author: Facundo Domínguez
published: true
tags:
  - announcement
---

A [new release] of Liquid Haskell is out after quite an active period of
development with [99 pull requests] in the `liquidhaskell` repository, and
[29 pull requests] in the `liquid-fixpoint` repository from about ten contributors.
This post, originally posted in the [Tweag blog], is to provide an overview of the changes that made it into the latest release.

[Tweag blog]: https://www.tweag.io/blog/2025-03-20-lh-release/
[new release]: https://hackage.haskell.org/package/liquidhaskell-0.9.10.1.2
[99 pull requests]: https://github.com/ucsd-progsys/liquidhaskell/pulls?q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06
[29 pull requests]: https://github.com/ucsd-progsys/liquid-fixpoint/pulls?q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06

There were contributions to the reflection and proof mechanisms; we got
contributions to the integration with GHC; the support of [cvc5] was improved
when dealing with sets, bags, and maps; and there was a rather [large overhaul][refactoring blog post]
of the name resolution mechanism.

[cvc5]: https://cvc5.github.io/

## Reflection improvements

Liquid Haskell is a tool to verify Haskell programs. We can write formal
specifications inside special Haskell comments `{-@ ... @-}`, and the tool
will check whether the program behaves as specified. For instance, the following
specification of the `filter` function says that we expect all of the elements
in the result to satisfy the given predicate.

```haskell
{-@ filter :: p:(a -> Bool) -> xs:[a] -> {v:[a] | all p v } @-}
```

Liquid Haskell would then analyze the implementation of `filter` to verify that
it does indeed yield elements that satisfy the predicate.

To verify such a specification, Liquid Haskell needs to attach a meaning to the
names in the predicate `all p v`. It readily learns that `p` is a parameter
of `filter`, and that `v` is the result. `all`, however, isn't bound by the specification's parameters, so it refers to whatever is in scope, which is the
Haskell function from the `Prelude`.

```haskell
all :: (a -> Bool) -> [a] -> Bool
```

And Liquid Haskell has a mechanism to provide logic meaning to the implementation
of a function like `all`, known as [reflection]. While it has always been convenient to reflect functions in modules analyzed by Liquid Haskell, it was not so easy when there was a
mix of local and imported definitions from dependencies that are not analysed with
Liquid Haskell. Last year, there was [an internship at Tweag] to address exactly this
friction, which resulted in [contributions][reflection contributions] to the
latest release.

[reflection]: https://ranjitjhala.github.io/static/refinement_reflection.pdf
[an internship at tweag]: https://www.tweag.io/blog/2024-09-12-lh-reflection/
[reflection contributions]: https://github.com/ucsd-progsys/liquidhaskell/pulls?q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06+author%3Ajarctan

## Reasoning and reflection of lambdas

The reflection mechanism also has other specific limitations at the moment. For instance,
it doesn't allow reflecting recursive functions defined in `let` or `where` bindings. And
until recently, it didn't allow reflecting functions that contained anonymous functions.
For example,

```haskell
takePositives = filter (\x -> x > 0)
```

In the latest release, we have [several contributions][lambda contributions] that introduce support for reflecting lambdas and improve the story for reasoning with them.
This feature is considered experimental at the moment, since we will still have usability and
performance concerns that deserve further contributions, but one can
already explore the experience that we could expect in the long run.

[lambda contributions]: https://github.com/ucsd-progsys/liquidhaskell/pulls?q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06+author%3AAlecsFerra

## Integration with GHC

In 2020 Liquid Haskell became a compiler plugin for GHC. It was hooked into the
end of the type checking phase firstly to ensure it only runs on well-typed programs,
and secondly, to ensure the plugin runs when GHC is only asked to typecheck the
module but not to generate code, which was helpful to IDEs.

For a few technical reasons, the plugin was re-parsing and re-typechecking the module
instead of using the abstract syntax tree (AST) that GHC handed to it as the result of
type checking. That is no longer the case in the latest release, where the AST after
type checking is now used for all purposes. In addition, there were [several improvements][ghc use improvements]
to how the `ghc` library is used.

[ghc use improvements]: https://github.com/ucsd-progsys/liquidhaskell/pulls?q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06+author%3Agergoerdi

## cvc5 support

Liquid Haskell offloads part of its reasoning to a family of automated theorem
provers known as SMT solvers. For most developments, Liquid Haskell has been
used with the [Z3] SMT solver, and this is what has been used most of the time in
continuous integration pipelines.

[z3]: https://github.com/Z3Prover/z3

In theory, any SMT solver can be used with Liquid Haskell, if it provides a standard
interface known as [SMT-LIB]. In practice, however, experiments are done with
theories that are not part of the standard. For instance, the reasoning capabilities
for bags, sets, and maps used to require `z3`. But now the latest release implements
[support][cvc5 support] for [cvc5] as well.

[smt-lib]: https://smt-lib.org
[cvc5 support]: https://github.com/ucsd-progsys/liquidhaskell/pulls?q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06+author%3Aclayrat

## Name resolution overhaul

Name resolution determines, for each name in a program, what is the definition that
it refers to. Liquid Haskell, in particular, is responsible for resolving names
that appear in specifications. This task was problematic when the programs
it was asked to verify spanned many modules.

There were multiple kinds of names, each with their own name resolution rules,
and names were resolved in different environments when verifying a module and
when importing it elsewhere, not always yielding the same results, which often
produced confusing errors.

Name resolution, however, was done all over the code base, and any attempt to
rationalize it would require a few months of effort. I started [such an epic] last
September, and managed to [conclude it][refactoring blog post] in February.
These changes made it into the latest release together with an awful lot of
[side quests] to simplify the existing code.

[refactoring blog post]: https://www.tweag.io/blog/2025-02-06-refactoring-lh/
[such an epic]: https://github.com/ucsd-progsys/liquidhaskell/issues/2169
[side quests]: https://github.com/ucsd-progsys/liquidhaskell/pulls?page=2&q=is%3Apr+is%3Aclosed+merged%3A2024-08-31..2025-03-06+author%3Afacundominguez

## The road ahead

There is no coordinated roadmap for Liquid Haskell. Much of the contributions
that it receives depend on the opportunity enabled by academic research or
the needs of particular use cases.

On my side, I'm trying to improve the adoption of Liquid Haskell. Much of the challenge
is reducing the amount of common workarounds that the proficient Liquid Haskeller
needs to employ today. For instance, supporting [reflection of functions in local bindings]
would save the user the trouble of rewriting her programs to put the recursive functions
in the top level.
Repairing the [support for type classes] would allow functions to be verified
even if they use type classes, which is a large subset of Haskell today.
And without having defined a scope with precision yet, Liquid Haskell still needs to
improve its user documentation, its error messages, and its tracing and logging.

The project is chugging along, though. It is making significant leaps in usability. The
upgrade costs [have been quantified][upgrade costs] for a few GHC releases, and
no longer look like an unbounded risk. The amount of external contributions has
increased last year, although we still have to see if it is a trend. And there is
no shortage of interest from academia and industrial interns.

Thanks to the many contributors for their work and their help during code
reviews. I look forward to learning what makes it into the coming Liquid Haskell releases!

[support for type classes]: https://github.com/ucsd-progsys/liquidhaskell/issues/2450
[reflection of functions in local bindings]: https://github.com/ucsd-progsys/liquidhaskell/issues/2480
[upgrade costs]: https://www.tweag.io/blog/2024-05-30-lh-upgrades/#the-hardest-test-failures
