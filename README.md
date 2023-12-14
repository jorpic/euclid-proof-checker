TODO: monadify proof checker
TODO: fuzzy tests: add random modifications to proofs and ensure that proof checking fails.

# euclid-proof-checker

Checking formal proofs of propositions from
Euclid's "Elements of Geometry.  Book 1".



http://www.michaelbeeson.com/research/FoundationsOfGeometry/index.php?include=CheckingEuclid
https://farside.ph.utexas.edu/books/Euclid/Elements.pdf
http://aleph0.clarku.edu/~djoyce/elements/bookI/bookI.html



-----------
http://www.michaelbeeson.com/research/talks/ProofCheckingEuclidSlides.pdf

Start of the proof of I.10
NEAB
ANELABC+TRABC proposition:01
ELABC
TRABC
NCABC defn:triangle
ANEEABBC+EEBCCA defn:equilateral
EEBCCA
EEACCB lemma:doublereverse
EEACBC lemma:congruenceflip
EQCB assumption
 COACB defn:collinear
 COABC lemma:collinearorder
NECB reductio
ANBECBD+EEBDAB postulate:extension
EEBDAB

Each line contains a statement, either a literal or a
conjunction or disjunction of literals.
◮ Proof by reductio and proof by cases are allowed.
◮ Each line is either justified or is an assumption (for reductio or
cases), or is a repeat of a previous line.
◮ initial unjustified lines repeat the hypotheses of the theorem.

-----------





Euclid after Computer Proof-Checking
http://www.michaelbeeson.com/research/papers/euclid2020.pdf


Foundations of geometry by david gilbert
https://www.gutenberg.org/files/17384/17384-pdf.pdf



