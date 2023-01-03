## Notes

This is an egg implementation of the *Routers* combinator calculus
described in [Liang, Jordan, Klein. "Learning Programs: A Hierarchical Bayesian Approach. ICML 2010"](https://people.eecs.berkeley.edu/~jordan/papers/liang-jordan-klein-icml10.pdf).

Figures 1 and 2 in the paper give a good idea of the calculus, and Figure 5 defined beta-reduction generally.

This calculus has the following properties that make it interesting for e-graphs and program synthesis:

1. Unlike named lambda calculus, it is canonical (so should get more sharing).
2. Unlike de Bruijn indices, beta-reduction does not modify the parts of the term that do not mention the formal being substituted (while de Bruijn needs to shift free vars of the body).
3. Beta-reduction still requires many local rewrites (like in lambda and de Bruijn), but those rewrites *only* propagate to subterms that actually mention the formal.
4. Only relevantly-typed terms are representable (i.e. we cannot represent a function that ignores its argument). This can a bad thing, depending on what you want to do, but for many synthesis purposes we actually work hard not to generate irrelevant terms, so this is good for synthesis.
5. At least in principle, beta-reduction rules look very easily invertible, which could be useful for library learning (this is what the original paper is about).

### Error in the original paper

The original paper has an error: in Fig. 5, which defines the beta-reduction rules. 
Consider the first rule, beta-reduction for the B router (other rules have the same error):

- Here the routers `r` for the "inner binders" of the abstraction are moved to the top, 
  but the variables that used to be routed right (to `y`) by `r` are now stuck.
- Hence `r1'` from the figure has to be extended with as many copies of `C` as there are inner binders that need to be routed to `y`.
- But that's not all! Inside `y` itself, the routers might now be in the wrong order,
  because as far as `y` in concerned, the formal under reduction comes before the inner binders,
  but in the reduced term it is now the other way around!
  My current approach is to create an adaptor term around `y` that swaps the order of the routers, but this increases the size of the reduced term.

**Example**

Let us first consider the following local reduction in named lambda calculus
(by "local" I mean that we are pushing the redex inwards towards the variables instead of doing the substitution in one step):

```
(\x y . f (x + y)) a
--> \y . f ((\x -> x + y) a)
```

Here `f` and `a` are some closed terms.

Note something important about the `x + y` subterm:
the order of bindings of its variables has switched as a result of this reduction
(`x` used to be the outer binder, but now it is the inner binder; so e.g. in de Bruijn notation their indices will have to be switched).


Now consider the same reduction in the Routers calculus (again, `f` amd `a` are arbitrary closed terms):

```
$. ($BB f ($CB ($B + I) I)) a
```

This matches the B-redex in Fig 5 with `?r0 = .`, `?r1 = .`, `?r = B`
(and also `?x = f`, `?y = ($CB ($B + I) I)`, `?z = a`).

If we use the rule from the paper, this would reduce to:

```
$B f ($. ($CB ($B + I) I) a)
```

But this term is ill-formed (and cannot even be translated to lambda), 
because the variable bound at the top level by `B` has no corresponding router in the "argument" `($. ($CB ($B + I) I) a)`.
The way to fix this is to replace the top-level `.` in the argument term with a `C`:
this is because this variable is destined to the `?y` part of the overall term,
which is now the left-hand side of the argument.
This would give us:

```
$B f ($C ($CB ($B + I) I) a)
```

This term is now well-formed, but it translates to the following lambda term:

```
\y . f ((\x . y + x) a)
```

But this is wrong! We got `y + x` instead of `x + y`!
This is because of the observation we made earlier: as a result of this reduction,
the order of the binders switches, but the term matched by `?y` still uses the old order!

We need to modify the term matched by `?y` from `($CB ($B + I) I)` to `($BC ($B + I) I)`
(in general, when multiple outer and inner binders are present, 
this transformation requires moving a binder from the middle of a router sequence to the end).

My implementation achieves this by wrapping the `?y` term in an adaptor term that swaps the order of the routers,
which in this case case would be `($BC ?y I)`.

In lambda notation:

```
original term:             (\x y . f (x + y)) a
desired result:            \y . f ((\x .             x + y) a)
result with adapter:       \y . f ((\x . ((\y'. x + y') y)) a)
```

As you can see in the last term, the order of bindings (of `x` and `y'`) is the same as the original term,
so `?y` can be used unchanged inside the adapter.

Unfortunately this increases the size of the reduced term *and* the number of binders,
although the binders are closer to the leaves, and that's why I thought it would be okay
(but somehow it isn't).

## Motivating Example

A potentially interesting motivating example for partial evaluation that I found in the paper "Practical Normalization by Evaluation for EDSLs".
This example is about partial evaluation of a branching program over arrays, where arrays are defined like so (in Haskell notation):

```
data Array a = Array
  { len :: Int
  , (!) :: Int -> a // infix function for accessing element at index
  }
```

Original program of type `Either Int Int -> Array Int -> Array Int`:

```
\scr arr ->
  map (+ 1) 
    (case scr of
      Left x -> map (+ x) arr
      Right _ -> arr)
```

Their technique evaluates this to:

```
\scr arr ->
  Array (len arr) (\i ->
    case scr of
      Left x -> (arr ! i) + x + 1
      Right _ -> (arr ! i) + 1
  )
```

I.e. it pushes the match inwards. This is nice from the standpoint of not having to allocate an intermediate array in the `Left` branch. But it's not so nice from the standpoint of having to match `len arr` times instead of just once. An alternative solution here would be:

```
\scr arr ->
  case scr of
    Left x -> Array (len arr) (\i -> (arr ! i) + x + 1)
    Right _ -> Array (len arr) (\i -> (arr ! i) + 1)
```

I.e. to push the match outwards. This is a bit longer, but it also avoids unnecessary allocation *and* only matches once.

I suspect that this choice cannot be easily made via NbE, but could be done with an e-graph, if we optimize for some resource consumption metric.

## TODO

- Why does the egraph blow up?
- Implement generic appliers for commutativy and associativity
