#import "@preview/theorion:0.4.1": *
#import "header.typ": *
#show: show-theorion

= Elementary Category Theory and Univalent Foundations
Lecture Notes \
Max Misterka

== Tentative Schedule
- Week 1 (Jan 12 - Jan 15):
  - Jan 12: Intro to Category Theory
  - Jan 13: Lec 1 continued; Universal Properties
  - Jan 14: Functors and Natural Transformations
  - Jan 15: Lec 3 continued
  - Jan 16: canceled due to lecturer availability

- Week 2 (Jan 20 - Jan 23)
  - Jan 19: canceled due to the holiday
  - Jan 20: Intro to Algebraic Topology and Homological Algebra (including applications of category theory)
  - Jan 21: Lec 5 continued
  - Jan 22: Yoneda Lemma; Enriched and Higher Category Theory
  - Jan 23: Intro to Topos Theory

- Week 3 (Jan 28 -- Jan 30)
  - Jan 26: canceled due to snow
  - Jan 27: Functors and Yoneda in Lean
  - Jan 28: Monads in Lean ("a monad is a monoid in the category of endofunctors")
  - Lectures will mostly consist of special topics and applications (order TBD), possibly including:
    - Category Theory in Deep Learning
    - Intro to Homotopy Type Theory
    - David Spivak's ideas
    - Connections to philosophy
  - Lectures will continue into February if there is interest in covering the missing topics.
- Recommended problem sets
  - One per week
  - One or two problems (some with multiple parts) from each lecture, for a total of 5-10 problems
  - Problems relating to a lecture will be written on the blackboard at the end of lecture and will be compiled at the end of the week on this document in the Problem Set sections

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
  - $Set$ (objects are sets, morphisms are functions)
  - $Grp$ (objects are groups, morphisms are group homomorphisms)
  - $AbGrp$ (objects are abelian groups, morphisms are group homomorphisms)
  - $Ring$ (objects are rings, morphisms are ring homomorphisms)
  - $K#h(-0.1em)Vect$, for a field $K$ (objects are vector spaces over $K$, morphisms are linear maps)
  - $Top$ (objects are topological spaces, morphisms are continuous functions)
  - $NN$ (objects are natural numbers, and there is a unique morphism $a -> b$ when $a <= b$ and no morphisms $a -> b$ when $a > b$, which makes there be only one choice for the composition operation)
  - $Trivial$ (one object $A$ with one morphism $1_A : A -> A$)
  - $G$, for any group $G$ (with one object $A$, and with one morphism $A -> A$ for each $g in G$, where composition is just the group operation)
]

*TODO: WRITE MORE ABOUT THESE CATEGORIES*

== Isomorphism

How can we generalize the idea of two sets, groups, etc. being isomorphic? Ideally we would define a notion of isomorphism between pairs of objects in a category $C$. This means that we need to state isomorphism purely in terms of the morphisms between sets, groups, etc., ignoring their set-theoretic elements. This can be done using inverse maps.

#definition(title: "isomorphism")[#emph[
  Two objects $A$ and $B$ in the object set of a category $C$ are isomorphic if there are morphisms $f : A -> B$ and $g : B -> A$ such that $f of g = 1_B$ and $g of f = 1_A$.
]]

This is the first example of a recurring trend: we will try to state many important properties of objects like sets, groups, rings, etc. using purely functions and function composition, while ignoring elements.

== Universal Constructions

*TODO: write out the formal definition of a product* (for now, just look at Wikipedia if you want to see it)

- Products

#image("images/product.png")

- Coproducts (duality)
- Initial objects and terminal objects
  - Initial: for every $X$ there is a unique morphism $I -> X$
- Equalizer (kernel of difference)

#image("images/equalizer.png")

- Tensor products (groups, rings, and vector spaces)

#image("images/tensor_product.png")

All of these constructions are unique up to isomorphism. This can be proved by noting that if we have two objects $P_1$ and $P_2$ which are both products, we have a morphism $P_1 -> P_2$ since $P_1$ maps into $X_1$ and $X_2$, but we also have a morphism $P_2 -> P_1$ since $P_2$ maps into $X_1$ and $X_2$, and the diagram commutes. Since these morphisms are the unique morphisms making this diagram commute, $P_1$ and $P_2$ are isomorphic. TODO expand this paragraph

== Functors

All of the objects (groups, rings, etc.) we were considering above have some kind of structure on top of a set. But you may have noticed that categories also have such a structure: they are a set of objects and a set of morphisms with the additional structure of the composition operator. So is there a notion of structure-preserving functions between categories? Yes, and it is called a functor.

#definition(title: "functor")[#emph[
  A functor $F : C -> C'$ from a category $C = (O, M, of)$ to a category $C' = (O', M', of')$ is a pair $F = (F_O, F_M)$, where $F_O : O -> O'$ and $F_M : M -> M'$, such that:
  - If $f in M$ then $dom(F_M (f)) = F_O (dom(f))$ and $cod(F_M (f)) = F_O (cod(f))$.
  - If $A in O$ then $F_M (1_A) = 1'_(F_O (A))$, where $1'$ denotes an identity morphism for an object in $C'$.
  - If $f, g in M$ such that $f of g$ is defined, then $F_M (f of g) = F_M (f) of' F_M (g)$.
]]

#example[
  Every category $C = (O, M, of)$ has a functor called the identity functor which maps objects to themselves and morphisms to themselves.
]

#example[
  The categories $Grp$, $AbGrp$, $Ring$, $KVect(K)$, $Top$ all have a functor $F$ from $C$ to $Set$ (where $C$ is one of the categories listed above) called the forgetful functor. The object map $F_o$ sends a group (or ring, or vector space, or topology) to its underlying set, and the morphism map $F_m$ sends a morphism to its underlying function. This functor effectively "forgets" the structure of the objects and morphisms of $C$, leaving behind the underlying $Set$-like structure.
]

We can now consider categories themselves as objects and functors as morphisms between these objects, allowing us to define the category of categories, $Cat$.

*TODO: discuss duality and natural transformations*

Note: Starting now, we will use $O(C)$ to denote the object set of a category $C$ and $M(C)$ to denote the morphism set of $C$ rather than writing $C = (O, M, of)$ for all categories.

In abstract algebra, it is useful to consider structure-preserving maps between algebraic structures. Similarly, in category theory, it is useful to consider functors, which are structure-preserving maps between categories. What happens if we extend this trend even further and try to construct a notion of structure-preserving maps between functors? Natural transformations accomplish this.

#definition(title: "natural transformation")[#emph[
  A natural transformation $eta$ between two functors $F : C -> C'$ and $G : C -> C'$ is an assignment of every object $A in O(C)$ to a morphism $eta_A in M(C')$ such that:
  - for every object $A$ of $C$, $eta_A : F(A) -> G(A)$
  - for every morphism $f : X -> Y$ of $C$, the following "square" diagram commutes:
  #image("images/natural.png")
  When $eta$ is a natural transformation from $F$ to $G$, we write $eta : F => G$.
]]

This is in some sense a structure-preserving map between functors, allowing us to construct a functor category $Fun(C, C')$ where the objects are all of the functors from $C$ to $C'$ and the morphisms are all of the natural transformations between such functors. Natural transformations will lead naturally to a discussion of enriched and higher category theory later in these notes.

#example[
  For every functor $F : C -> C'$, there is an identity natural transformation $1_F : F => F$. To define a natural transformation, we need to assign to every object $X$ of $C$ a morphism $(1_F)_X : F(X) -> F(X)$, and we do this by letting $(1_F)_X$ be the identity map $1_(F(X))$.
]

#example[
  In linear algebra, you may have heard that there is a "natural" isomorphism between any finite-dimensional vector space and its double dual, or that there is a "natural" linear map from any vector space into its double dual. It turns out that "natural" can be formalized using natural transformations, as we will see below.
  
  In $KVect(K)$, there is a functor $D$ called the double dual, which maps a vector space $V$ to $V^(**)$, the dual of the dual of $V$, and maps a linear map $f : V -> W$ to the induced map $f^(**) : V^(**) -> W^(**)$. What it means for the linear map $V -> V^(**)$ to be "natural" is that it comes from a natural transformation $eta : 1_KVect(K) => D$. To define $eta$, note that for every vector $v in V$ we have an "evaluation map" $eval_v : V^* -> V$ defined by $eval_v (phi) = phi(v)$. You can check that this is linear. But a linear map from $V^*$ to $V$ is just an element of $V^(**)$ by definition, so $eval_v in V^(**)$, meaning that we have a map $V -> V^(**)$ defined by $v |-> eval_v$. This map also turns out to be linear. Letting $eta_V$ be this map gives us a natural transformation $eta : 1_KVect(K) => D$, as desired. When $V$ is finite-dimensional, a basis argument shows that $eta_V$ is an isomorphism, which is why $V$ and $V^(**)$ are "naturally" isomorphic in the finite-dimensional case.

  *TODO: write the detailed proof that $eta$ is natural*
]

== Problem Set 1

All of the exercises require answering with a proof for a fully complete answer, but an intuitive justification is good enough if your main goal is to learn the intuition of category theory rather than the entire subject.

1. Prove that for the category of sets, the map $Q -> S times T$ in the definition of the product is unique.
2. Do all categories have at least one product?
3. In general, what is the equalizer between two linear maps in $KVect(K)$?
4. #enum(
  [Do all pairs of objects in $Set$ have a coproduct? If so, what is it?],
  [What about in $Grp$?],
  [What about in $KVect(K)$?],
  [What about in $NN$ (which is defined in these notes)? What about in the opposite category of $NN$?],
  numbering: "(a)"
)
5. Construct a functor from $KVect(K)$ to its opposite category. Is $KVect(RR)$ isomorphic (as an object of $Cat$) to its opposite category?
6. Find a natural transformation between the identity functor $1_Grp : Grp -> Grp$ and the abelianization functor $Ab : Grp -> Grp$. The functor $Ab$ is defined so that $Ab_o (G) = G\/[G,G]$, where $ [G,G] = lr(chevron.l x y x^(-1) y^(-1) | x, y in G chevron.r), $ and if $f : G -> H$, then $Ab_m (f)$ is the map $G\/[G,G] -> H\/[H,H]$ induced by $f$.

== Algebraic Topology

Algebraic topology is a field of math which uses tools from abstract algebra to study topological spaces. It is also one of the main applications of category theory within pure math (the other being algebraic geometry). Here, we will quickly go through some important concepts in topology and then introduce algebraic topology.

#definition(title: "topological space")[#emph[
  A topological space is a set $X$ of "points" along with a set $cal(T)$ of "open sets" whose elements are subsets of $X$, such that:
  - $emptyset in cal(T)$ and $X in cal(T)$,
  - The union of any collection of sets in $cal(T)$ is also in $cal(T)$,
  - The intersection of any _finite_ collection of sets in $cal(T)$ is also in $cal(T)$.
  If these conditions are satisfied, $cal(T)$ is called a topology on $X$.
]]

Intuitively, this generalizes the concept of an open subset of $RR^n$. Recall that a subset $U subset.eq RR^n$ is open if and only if for every $x in U$ there exists a radius $r$ such that the ball of radius $r$ centered at $x$ is fully contained in $U$. You can check that the set of all open subsets of $RR^n$ satisfies the three properties listed above, and is therefore a topology on $RR^n$ (although not the only possible topology). This topology is called the standard topology, and when we call $RR^n$ a topological space we will assume that we are using the standard topology.

It turns out that a lot of the concepts from real analysis generalize to the setting of arbitrary topological spaces. For example, the following definition generalizes continuity:

#definition(title: "continuous function")[#emph[
  Let $X$ and $Y$ be topological spaces. A function $f : X -> Y$ is continuous if for all open sets $U subset.eq Y$, the preimage $f^(-1) (U)$ is open in $X$.
]]

This corresponds to the usual definition of continuity when using the standard topology on $RR^n$. To see this, think about open sets in $RR^n$ as unions of open balls. Then, this definition is equivalent to saying that if $f$ maps a point $x$ to a point $y$, then no matter how small an open ball $U$ we make around $y$, we can always find an open ball $V$ around $x$ which gets mapped by $f$ into $U$. The radii of the balls $U$ and $V$ correspond to $epsilon$ and $delta$ from real analysis.

Now we can define $Top$, the category of topological spaces. Its objects are all topological spaces and its morphisms are continuous functions between them, with composition defined as it usually is for functions. This will be useful later.

Before we jump into algebraic topology, there are a few definitions we need.

#definition(title: "subspace topology")[#emph[
  Let $X$ be a topological space with topology $cal(T)$. Then, for any subset $Y subset.eq X$, we define the subspace topology on $Y$ to be $ cal(T)' = {U inter Y | U in cal(T)}. $
]]

This can be shown to be a topology on $Y$, so any subset $Y$ of a topological space $X$ is a topological space under the subspace topology.

Consider the topological spaces $S^2$ and $T^2$, where $S^2$ is the $2$D surface of the sphere in $RR^3$, and $T^2$ is the $2$D surface of the torus in $RR^3$, both using the subspace topology induced by the standard topology on $RR^3$. Are $S^2$ and $T^2$ isomorphic as objects of $Top$? Intuitively they are not, because the torus has a hole while the sphere does not. But how do we prove this? One approach is to find a property which is preserved under $Top$ isomorphisms but which exactly one of $S^2$ and $T^2$ satisfies. Such a property is given below.

We want to capture the idea of a subset of $RR^3$ having a hole, because $T^2$ has a hole but $S^2$ does not. The challenge is expressing this in topological language in a way that is preserved under isomorphism. The way we do this is by defining a topological space $X$ to have a hole if it has a loop which cannot be continuously contracted to a point. We must now define what a "loop" is, and what it means to "continuously contract" one.

*TODO: introduce the fundamental group and homotopy groups, and explain why this is a functor $Top -> Grp$*

#image("images/simplicial_chain.png")

#image("images/boundaries.png")

*TODO: introduce simplicial homology, singular homology, and the functors $Delta -> Top$ and $H_n : Top -> AbGrp$, and the natural transformation $H_n => H_(n-1)$*

#image("images/singular.png")

See https://ocw.mit.edu/courses/18-905-algebraic-topology-i-fall-2016/resources/mit18_905f16_lec8/

== The Yoneda Lemma

Here $h_A$ is the Hom-functor in a locally small category (which is a category where between a pair of objects, the morphisms can be put into a set): $ h_A (B) = Hom(A, B) = {"morphisms" f : A -> B "in" C}. $

#image("images/yoneda.png")

This generalizes Cayley's theorem from group theory. If the category $C$ is the one-object category constructed from a group $G$, then a functor $F$ from $C$ to $Set$ is just a group action of $G$ on some set $S$. Each object Letting $A$ be the unique object of $C$, Yoneda implies that $Nat(h_A, F)$ is in bijection with $F(A)$. But $F(A)$ is just our set $S$, and $h_A$ can only take in $A$ and output $h_A (A) = Hom(A, A) = G$. So a natural transformation $eta : h_A => F$ must consist of a single map $eta_A : A -> A$ such that for any $f : A -> A$, we have $eta_A of h_A (f) = F(f) of eta_A$. Morphisms $f : A -> A$ are just group elements $g$, and $F$ maps a group element $g$ to its corresponding permutation of the elements of $S$ under the group action. Also, $h_A$ maps $g$ to the map $G -> G$ given by $g' |-> g of g'$. But composition here is just the group operation. So we have that $eta_A (g dot g') = g dot eta_A (g')$, where the $dot$ on the left is the group operation and the dot on the right is the group action. Here $eta_A : G -> S$. Plugging in $g' = e$ gives $eta_A (g) = g dot eta_A (e)$, which causes the condition reduces to $g dot g' dot eta_A (e) = g dot g' dot eta_A (e)$, so this is necessary and sufficient. This means that these natural transformations are given by a single choice of element $eta_A (e) in S$. This proves the lemma for this specific case, and it also shows how it is related to Cayley's theorem: if we set $F = h_A$, then natural transformations from $h_A$ to $F$ can be composed with each other, giving a group structure. This group is a subgroup of the permutation group on the elements of $G$, since each natural transformation consists of a function $eta_A : G -> G$. Also, the map provided by Cayley's theorem happens to be a homomorphism in this case, showing that $G$ is isomorphic to a subgroup of its permutation group.
