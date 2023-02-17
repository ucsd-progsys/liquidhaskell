
![LiquidHaskell Logo](static/img/logo.png)

LiquidHaskell _(LH)_ refines Haskell's types with logical predicates that let you enforce important properties at compile time.

# Guarantee Functions are Total

<div class="example-row">
<p>
LH warns you that head is not total as it is missing the case for <code>[]</code> and checks that it is total on <code>NonEmpty</code> lists.
<a href="blogposts/2013-01-31-safely-catching-a-list-by-its-tail.lhs">(more...)</a>
</p>
<img src="static/img/splash-head.gif">
</div>

<div class="example-row">
<img src="static/img/splash-unstutter.gif">
<p>
The input contract propagates to uses of <code>head</code> which are verified by ensuring the arguments are <code>NonEmpty</code>. 
</p>
</div>

# Keep Pointers Within Bounds

<div class="example-row">
<p>
LH lets you avoid off-by-one errors that can lead to crashes or buffer overflows.
<a href="blogposts/2013-03-04-bounding-vectors.lhs">(more...)</a>
</p>
<img src="static/img/splash-vectorsum.gif">
</div>

<div class="example-row">
<img src="static/img/splash-dotproduct.gif">
<p>
Dependent contracts let you specify, e.g. that <code>dotProduct</code> requires equal-sized vectors.
</p>
</div>

# Avoid Infinite Loops

<div class="example-row">
<p>
LH checks that functions terminate and so warns about the infinite recursion due to the missing case in <code>fib</code>.
<a href="tags.html#termination">(more...)</a>
</p>
<img src="static/img/splash-fib.gif">
</div>

<div class="example-row">
<img src="static/img/splash-merge.gif">
<p>
<em>Metrics</em> let you check that recursive functions over complex data types terminate. 
</p>
</div>

# Enforce Correctness Properties

<div class="example-row">
<p>
Write correctness requirements, for example a list is ordered, as refinements. LH makes illegal values be <em>unrepresentable</em>.
<a href="blogposts/2013-07-29-putting-things-in-order.lhs">(more...)</a>
</p>
<img src="static/img/splash-ups.gif">
</div>

<div class="example-row">
<img src="static/img/splash-insertsort.gif">
<p>
LH automatically points out logic bugs, and proves that functions return correct outputs <em>for all inputs</em>. 
</p>
</div>

# Prove Laws by Writing Code

<div class="example-row">
<p>
Specify <em>laws</em>, e.g. that the append function <code>++</code> is associative, as Haskell functions. 
</p>
<img src="static/img/splash-assocthm.gif">
</div>

<div class="example-row">
<img src="static/img/splash-assocpf.gif">
<p>
Verify laws via <em>equational proofs</em> that are plain Haskell functions. Induction is simply recursion, and case-splitting is just pattern-matching. 
</p>
</div>

# Get Started

The easiest way to try LiquidHaskell is [online, in your browser](http://goto.ucsd.edu:8090/index.html). This environment is ideal for quick experiments or following one of the tutorials:

* The [Official Tutorial](https://ucsd-progsys.github.io/intro-refinement-types/120/) (long but complete) (has interactive exercises)
* [Andres Loeh's Tutorial](https://liquid.kosmikus.org) (concise but incomplete)

For links to more documentation, see the nav-bar at the top of this page.

# Get Involved

If you are interested in contributing to LH and its ecosystem, that's great!
We have more information on our [GitHub repository](https://github.com/ucsd-progsys/liquidhaskell).
