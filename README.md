# CuteCAS
Abstract Algebra for [FStar](https://www.fstar-lang.org/)

# What's this?

For now, just a sandbox where I play with F* and try implementing abstract algebra notions there.
Some files here are future parts of F* core library (some are already there).
I will eventually remove those that are already part of fstar's ulib.

# What's done already?

* abstract equivalence relation (symmetric, reflexive, transitive function of type `t -> t -> bool`);
* binary operations (with lemmas on commutativity, associativity, neutral elements, absorbers, inverses);
* grouplike structures (magma -> semigroup -> monoid -> group) with separately defined commutative versions;
* ringlike structures (ring -> domain -> euclidean domain -> skewfield -> field) with distributivity lemmas and unit/normal decomposition for euclidean domains;
* fields of fractions (over arbitrary integral domains)
* commutative rings of polynomials (over arbitrary commutative rings)

# What's next?

* completing framework for euclidean domains (div/rem, gcd/eea)
* enhancing fields of fractions over euclidean domains by introducing the reduced fractions via EEA/GCD
* introduce the notion of polynomial ring over a field, prove it to be a domain, and provide the framework for it
* head towards differential fields. See my [F# CAS sketch](https://github.com/hacklex/AbstractMathTypes) for details

# What could I use this for?

Currently, this is not usable. It still lacks key features and functions, and the code itself is still a mess.
I rewrite and refine it as the time permits (since it's just my pet project), but overall, lots of stuff in the files is still
very chaotic and unreadable. Still, even though I work on adding comments and prettifying the code, I prioritize 
getting it to work well over getting it to look nicely. After all, a lot of lemmas currently take too much resources
and require ridiculous values of `z3rlimit` to be verified.

# This F* code is BAD!

I know. It quite probably is. I'm currently learning the language and would be glad to improve the code if you tell me 
what exactly can be improved here, and how. So, feel free to drop an issue, or make a pull request, or just fork and 
then show me something good, if you feel like it.

In fact, you might even notice how the code gets better as I advance from basic stuff like semigroups to slightly more advanced 
stuff like proving certain properties of a field of fractions. That is because I gain experience in the process of writing this 
framework, and the further I advance, the better my code becomes. 

I'd love to get the feedback on the code quality. Don't hesitate, don't pull the punches. I only aim to get better with this language :)

# UPD. March 2022: Polynomial ring is completed

Alright, I've finally pulled it. The last boss that is polynomial multiplication associativity, has been finally conquered.
Had to carefully construct a 3D matrix from the three polynomials, assert that its fold would equal the three polynomials product
in both multiplication orders, and apply transitivity to assert that multiplication in both orders yields equivalent results.

More than hundred lines of the main lemma. Another hundred buried in auxiliaries. That was the largest proof I've completed so far :)

# Riding to F* core

It seems like the guys from F* team liked my algebra types, so these types will eventually become part of F*'s standard library.