## Notes

This is an egg implication of the /Routers/ combinator calculus
described in Liang, Jordan, Klein. "Learning Programs: A Hierarchical Bayesian Approach. ICML 2010".

This calculus has the following properties that make it interesting for e-graphs and program synthesis:

1. Unlike named lambda calculus, it is canonical (so should get more sharing).
2. Unlike de Bruijn indices, beta-reduction does not modify the parts of the term that do not mention the formal being substituted (while de Bruijn needs to shift free vars of the body).
3. Beta-reduction still requires many local rewrites (like in lambda and de Bruijn), but those rewrites *only* propagate to subterms that actually mention the formal.
4. Only relevantly-typed terms are representable (i.e. we cannot represent a function that ignores its argument). This can a bad thing, depending on what you want to do, but for many synthesis purposes we actually work hard not to generate irrelevant terms, so this is good for synthesis.
5. At least in principle, beta-reduction rules look very easily invertible, which could be useful for library learning (this is what the original paper is about).

### Error in the original paper

The original paper has an error: in Fig. 5, which defines the beta-reduction rules). 
Consider the first rule, beta-reduction for the B router:

- Here the routers `r` for the "inner binders" of the abstraction are moved to the top, 
  but the variables that used to be routed right (to `y`) by `r` are now stuck.
- Hence `r1'` from the figure has to be extended with as many copies of `C` as there are inner binders that need to be routed to `y`.
- But that's not all! Inside `y` itself, the routers might now be in the wrong order,
  because as far as `y` in concerned, the formal under reduction comes before the inner binders,
  but in the reduced term it is now the other way around!
  My current approach is to create an adaptor term around `y` that swaps the order of the routers, but this increases the size of the reduced term.


## TODO

- Why does the egraph blow up?
- Implement generic appliers for commutativy and associativity