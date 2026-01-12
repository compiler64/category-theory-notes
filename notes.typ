#import "header.typ": *

= Elementary Category Theory and Univalent Foundations
Lecture Note 1 \
Jan 12, 2026 \
Max Misterka

== What is Category Theory?
Consider the following mathematical objects:
- Sets
- Groups
- Rings
- Topological spaces
Hopefully, if you're in this class, you've heard of at least one of these mathematical objects. If you're familiar with multiple, then you may have noticed some similarities between them:
- The objects are generally sets with extra structure.
- There are "special functions" between two objects which preserve the structure of the objects:
  - Sets: functions
  - Groups: group homomorphisms
  - Rings: ring homomorphisms
  - Vector spaces: linear map
  - Topological spaces: continuous functions
- There is some notion of "equality" between pairs of objects:
  - Sets: bijections
  - Groups: group isomorphisms
  - Rings: ring isomorphisms
  - Vector spaces: vector space isomorphisms
  - Topological spaces: homeomorphisms

Category theory provides a general way to think about all of these classes of objects at once. It is extremely useful in algebraic geometry and algebraic topology, and a few applications have been found outside of math, as we will see later in the course.

== Basic Definitions

#definition(title: "category")[#emph[
  A category $C = (O, M, of)$, where $O$ is a collection of "objects," $M$ is a collection of "morphisms" between objects, and $of$ is an operator that "composes" two morphisms. These must satisfy the following properties:
  - Each morphism $f in M$ is assigned to a "domain" object $dom(f) in O$ and a "codomain" object $cod(f) in O$. If $dom(f) = A$ and $cod(f) = B$, we write $f : A -> B$.
  - If $f : A -> B$ and $g : B -> C$, then the composition operator produces a morphism $g of f : A -> C$.
  - (Identity) For each object $A in O$, there is an identity morphism $1_A : A -> A$ which acts like an identity for the composition operator:
    - if $f : A -> B$ then $f of 1_A = f$,
    - if $g : B -> A$ then $1_A of g = g$.
  - (Associativity) If $f : A -> B$, $g : B -> C$, and $h : C -> D$, then $(h of g) of f = h of (g of f)$.
]]

#example[
  The following are examples of categories:
  - $Set$
  - $Grp$
  - $Ring$
  - $Vect$
  - $Top$
]
