# CuteCAS
Abstract Algebra for FStar

# What's this?

For now, just a sandbox where I play with F* and try implementing abstract algebra notions there.

# What's done already?

* abstract equivalence relation (symmetric, reflexive, transitive function of type `t -> t -> bool`);
* binary operations (with lemmas on commutativity, associativity, neutral elements, absorbers, inverses);
* grouplike structures (magma -> semigroup -> monoid -> group) with separately defined commutative versions;
* ringlike structures (ring -> domain -> euclidean domain) with distributivity lemmas and unit/normal decomposition for euclidean domains;
* started working with abstract fractions over euclidean domains (still need to generalize over arbitrary integral domains)

# What's next?

* completing framework for euclidean domains (div/rem, gcd/eea)
* completing framework for abstract fractions (need to prove that they form a field, and implement reduced fractions wherever eea/gcd is available)
* introduce the notion of polynomial ring over a field, prove it to be a domain, and provide the framework for it
* head towards differential fields. See my [F# CAS sketch](https://github.com/hacklex/AbstractMathTypes) for details

# What could I use this for?

Currently, this is not usable. It still lacks key features and functions, and the code itself is still a mess.
I rewrite and refine it as the time permits (since it's just my pet project), but overall, lots of stuff in the files is still
very chaotic and unreadable. Still, even though I work on adding comments and prettifying the code, I prioritize 
getting it to work well over getting it to look nicely. After all, a lot of lemmas currently take too much resources
and require ridiculous values of `z3rlimit` to be verified.

# This F* code is BAD!

I know. It quite probably is. I'm currently learning the language and would be glad to improve the code if you tell me what exactly can be improved here, and how.
So, feel free to drop an issue, or make a pull request, or just fork and then show me something good, if you feel like it.
