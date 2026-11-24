#import "@preview/physica:0.9.8": *
#import "@preview/fletcher:0.6.0" as fl
#import "@preview/curryst:0.6.0" as cr
#import "@preview/clean-acmart:0.0.1": acmart, acmart-ccs, acmart-keywords, acmart-ref, to-string

// Custom Macros

#let hidden = (x) => []

#let iso = math.tilde.equiv
#let hom =  fl.edge.with(in-math: true)
#let isWeakerThan = (
  eq: math.subset.eq.sq,
)
#let isWeakerThan = math.subset.sq
  // eq: (
  //   not: $subset.eq.not.sq$
  // )

#let gesr = $"GES"_rho$
#let play = math.triangle.l

#show math.equation.where(block: true) : set block(above: 0.75em)
#show figure: set block(above: 1em, below: 0.5em)


// Setup for template

#let title = [
  Plug and Play: Modular Semantics for Hybrid Quantum Programming Languages
]
#let authors = (
  (
    name: [Jacob Trevor],
    email: [j.trevor.1@research.gla.ac.uk],
    department: [School of Computer Science],
    institute: [University of Glasgow],
    city: [Glasgow],
  ),
)

#let conference = (
  name:  [Super Cool Conference],
  short: [SCC '28],
  year:  [2026],
  date:  [December 2026],
  venue: [Glasgow, UK],
)

#let ccs = (
  (
    generic: [Software and its engineering],
    specific: ([Virtual machines], [Virtual memory], ),
  ),
  (
    generic: [Computer systems organization],
    specific: ([Heterogeneous (hybrid) systems], ),
  ),
)

#show: acmart.with(
  title: title,
  authors: authors,
  conference: conference,
  doi: "https://doi.org/10.1145/0000000000",
  copyright: "cc",
  keywords: ("Virtual machine", "Virtual memory", "Operating system"),
  // Set review to submission ID for the review process or to "none" for the final version.
  // review: [\#001],
)

= Abstract 

#hidden[
Hybrid Quantum Programming Languages (HQPL) are ...
// 
We provide a way to _add languages together_, and, when certain preconditions are met, to automatically derive the semantics of the result from the semantics of the component parts.
// 
TODO: We show some simple subsumption results.
]


= Introduction

Consider the following two toy programs:
// 
#grid(columns:(1fr, 1fr), [
Program A: 
```
H 0; H 0
```
],[
Program B:
```
H 0; H 0; Meas 0
```
])


Program A is written in a language called _Unitary,_
which allows us to sequence gate applications.
// 
It applies the hadamard gate to qubit 0 twice.
// 
Program B is written in a language called _Circuit,_ which allows gate applications as well as effectful (i.e. non-recorded) measurement.
// 
It also applies the hadamard gate to qubit 0 twice, but then measures qubit 0.
// 
Every _Unitary_ program is also a valid _Circuit_ program --- _Circuit_ syntactically subsumes _Unitary._
// 
Conveniently, the semantics also matches up, in the sense that the semantics of a program in _Unitary_ matches (in some sense) its semantics when interpreted as a program in _Circuit._
// 
To be specific, we can give the semantics of _Unitary_ concretely, in terms of a matrix:

$
  "UApp"_n (U) &:= U ; U | G arrow(x)\
  "UApp"_n [|-|] &: CC^(2^n)\
  "UApp"_n [| a; b |] &:= [|b|] dot [|a|]\
  "UApp"_n [|G arrow(x)|] &:= pi(arrow(x))^(-1) compose arrow.t G compose pi(arrow(x))\
$

That is to say, for any gate application, we can concretely compute a matrix which represents its action on some quantum state. 
// 
A program $P$ can be seen as a function $ket(psi) |-> [|P|] ket(psi)$.
// 
With a little manual calculation, we can see that the semantics of Program A is:
$
[| "Prog. A" |]_1 = H dot H = mat(delim:"[", 1,0;0,1)
$


However, when we introduce measurement to our language, things become slightly more complex.
// 
We require a richer representation to handle the multiple possible outcomes of measurement.
// 
We can give a semantics as a completely positive trace-preserving (CPTP) map on density operators:
$
  "Circ"_n (C) &:= &&C; C | G arrow(x) | M x\ \
  "Circ"_n [|-|] &: &&CC^(2^n times 2 ^n) -> CC^(2^n times 2 ^n)\
  "Circ"_n [| a; b |] &:= &&[|b|] compose [|a|]\
  "Circ"_n [|G arrow(x)|] &:= &&
  "let" G' :=  pi_N^(-1) arrow(q) dot arrow.t^N G dot pi_N arrow(q)'\ 
  & "in" &&lambda rho. G rho G^dagger\
  "Circ"_n [| M x|] &:= &&lambda rho . sum_(i in "t", "f") P_i rho P_i^dagger 
$

We can use this to write down functions that represents the semantics of both Program A and Program B:
$
  [| "Prog. A" |] &= lambda rho . (H(H rho H^dagger)H^dagger) 
  = lambda rho. rho \ 

  [| "Prog. B" |] &= lambda rho . sum_(i in "t", "f") P_i (H(H rho H^dagger)H^dagger) P_i^dagger \
  &= lambda rho. sum_(i in "t", "f") P_i rho P_i^dagger
$

Note that where in the matrix semantics, program A denoted the identity matrix, in the CPTP map semantics it denotes the identity function. 
// 
We will make the exact sense in which the semantics correspond precise in the course of the paper, but note the intuitive connection for now.

The CPTP map semantics of _Circuit_ are more expressive than the matrix semantics of _Unitary_.
// 
However, this expressiveness comes at a cost.
//
To compare programs in _Unitary,_ we simply compare their denotations directly.
// 
Considering only the comparison of the denotations, this requires $2^n times 2 ^n$ comparison operations, where $n$ is the number of qubits in the circuit.


We can do the same for the semantics of circuit, though we must use the Choi matrix representation of CPTP maps.
// 
Ignoring for now the details of constructing the Choi matrix, this results in a matrix of size $2^(2n) times 2^(2n)$.
// 
This represents a quadratic slowdown, compared to checking in _Unitary._
// 
However, the semantics of the two languages are compatible in such a way that if we know that a given pair of programs are equivalent in _Unitary,_ then we know that the corresponding pair of _Circuit_ programs must also be equivalent.

The purpose of this work is to formalise the intuitions I have just alluded to --- that _Unitary_ is somehow _embedded_ into _Circuit_ in a sensible way --- and then exploit this fact to derive faster judgements of program equality.
// 
This is the most obvious material benefit, but there are others.
// 
The way in which we formalise this leads to a natural notion of _deriving_ semantics --- meaning that we do not need to re-define the semantics of unitary applications for each language we wish to include them in.
// 
Whilst these advantages are clear for this concrete example, the technique I present can be generalised to more complex languages and other semantic domains.


== Contributions:

1. A framework for constructing modular syntax, based on _Data Types a la Carte_ @dtalc and _containers_ @Abbott_Altenkirch_Ghani_2005

2. For languages produced by this framework, we show:
  1. Each has a normal form 
  2. How to calculate its semantics from the semantics of its input features
  3. Confluence of semantics when multiple derivations are possible

3. An application of this theory to the domain of quantum programming languages. In so doing:
  1. We provide a formalisation of the underlying quantum information theory in lean 
  2. We show a practical application of this framework to use in verified optimisation or program rewriting.

All of our major results are mechanised in the lean theorem prover.

= Notation

We shall use $plus.o$ to denote the _coproduct_ of two objects.
// 
This can be seen as a bifunctor $cal(C) times cal(C)^op -> cal(C)$.
// 
Also important is the copairing operation, written $[-, -]$.
// 
This represents the universal morphism making the following diagram commute:

#figure[
  #fl.diagram($
      A hom("r", "->", label:"inl") hom("dr", "->", f, label-side: #left)
    & A plus.o B hom("d", "-->", [f, g], label-side: #center)
    & B hom("l", "->", label:"inr") hom("dl", "->", g, label-side: #right)\ 
    & C
  $)
]


= Modular Syntax with Containers

In order to discuss a modular semantics, we must first have a modular syntax. 
// 
The essential problem of defining syntax in a modular manner was put clearly by Wadler:
// 
#quote[
  The goal is to define a datatype by cases, where one can add new cases to the datatype and new functions over the datatype, without recompiling existing code, and while retaining static type safety (e.g., no casts).
]
// 
This is known as _the expression problem,_ as expressions are a classic case where such a modular datatype is useful.


Swierstra offered a solution to the expression problem in his paper _Data Types a la Carte_ (DTalC) @dtalc.
// 
The idea is to define sets of constructors as _endofunctors_ over the type of subterms.
// 
To take a combination, we define a coproduct over these functors, yielding a new functor.
// 
Given a functor, the actual composite datatype is taken to be the functors fixpoint.
//
Intuitively, this corresponds to expressions having further expressions as subterms, which in turn have expressions as subterms, and so on.


For us, setting up a collection of functors corresponds to splitting a language up into a set of _syntactic features,_ which can be combined to produce a composite languages.
// 
However, there are some issues with Swierstra's presentation.
// 
The biggest obstacle is that the `Fix` function, defined `Fix f = f (Fix f)`, is not terminating.
// 
Lean disallows non-total definitions like this, as they produce an inconsistent system.


Thus, we require an alternative way to handle the problem.
// 
Containers @Abbott_Altenkirch_Ghani_2005 provide a natural way to approach this. 
// 
One can think of a container as a _template,_ specifying some _type of constant data_ and for each, a _type of holes_ which must be filled.
// 
Let us consider for example _sequencing_ as a container.
// 
The constant data need only track that the expression is a sequencing.
// 
One could think of this as a type (`Seq'`) with a single nullary constructor (`mk`).
// 
There are two holes --- the program to execute first, and the program to execute second.
// 
We can represent this diagrammatically, using "\_" for holes:
// 
$ \_ ; \_ $
// 
Or formally, in lean:

```lean
structure Container where
  shape : Type
  pos : shape -> Type

inductive Seq where | mk : Seq

def Seq : Container := { 
  shape := Seq 
  pos _ := Fin 2
}
```

== Categorical presentation 

Categorically, we can see containers as a pair of objects.
// 
The shapes are represented by an object $"Sh" : cal(C)$ of the base category.
// 
the positions are defined by a morphism in the slice category $p : cal(C)_(\/"Sh")$.
// 
We can understand $PP$ to be the type of all possible positions in all possible shapes. 
// 
The morphism $p : PP -> "Sh"$ associates with each position a shape --- i.e. it defines which shape a given position is associated with.
// 
Given a concrete shape $s : top -> "Sh"$, the type of positions for that shape is given by a pullback:

#figure()[#fl.diagram($
    PP 
      hom("r", "<-") 
      hom("d", "->", label: p) 
  & P s    
      hom("d", "->", label: !) 
  \ "Sh"
      hom("r", "<-", label: s) 
  & top
$)]


== Constructions on Containers

There are two key constructions on containers that we need:
// 
Firstly, it's possible to take the coproduct of two containers, yielding a new container. 
// 
Secondly, it is possible to take the (constructive) fixpoint of a container, and thus generate the relevant AST type.


Containers have a notion of coproduct, which we shall write $":+:"$.
// 
The coproduct of two containers is itself a container, the shape of which is the regular coproduct of the two input shapes.
// 
To define the position function, we use the copairing construction; when we have a left shape, we use the left position function. 

$
  (S_1 play P_1) ":+:" (S_2 play P_2) = (S_1 plus.o S_2) play [P_1, P_2]
$

This gives us a way to compose features together.
// 
However, I have not yet shown how containers can be seen to 'contain' anything.
// 
Intuitively, we want to define a way to _fill the holes_ of the container, much like you you can replace the blanks of the template with real data.
// 
For this, we turn to the _extension_ of a container.
// 
Every container defines a functor, which we call its extension.
// 
To take the extension of a container _into_ some type $X$, we must provide a _shape_ of the container, and then, for each position in that shape, we must provide a value drawn from $X$.
// 
Intuitively, given a container $C$ and a type $X$, we form a new type $[|C|]X$.
// 
As extension is a functor, there must also therefore be a way to lift functions $f : A -> B$ to $[|C|] f : [|C|] A -> [|C|] B$.

$
  [|S play P|] X = Sigma" "s:S, (P s -> X) 
$

The trick we have played is identical to the one Swierstra uses; 
our features are now functors over the type of subterms.
// 
The obvious question to ask is now how to take the _fixed point_ of this functor,
to generate the AST type. 
// 
For a container $C$, this is written $mu C$ and is always guaranteed to exist:
$
  mu (S play P) = mu X. Sigma" "s:S, (P s -> X) 
$

== Features for a Quantum Programming Language

Our task now is to find a suitable set of syntactic features for quantum programming.
// 
We require 3:
// 
Sequencing, which we have already seen, as well as unitary application and measurement.
// 
Unitary application and measurement are both examples of _terminal features._
// 
There are no subterms.
// 
Instead, there is rather more structure in the constant data instead.


We will work in a fixed bit-width setting. 
// 
Practically, this means that the type of programs is a family over $NN$ i.e. $"programs" : NN -> "Type"$.
// 
You can think of a $"program" n$ as being a circuit of width $n$.


To measure a qubit, we must know which qubit to target.
// 
On a circuit of width $n$, this is a value of type $"Fin" n$.
// 
Thus, the constant data for measurement is simply $"Fin" n$


The situation for unitary application is similar, but more complicated.
// 
First, of course, we must know what gate to apply. 
// 
This gate will be itself associated with a size $w$.
// 
We then need an ordered list of $w$ targets, each of which must be a distinct member of $"Fin" n$. 
// 
The simplest way to set this up in lean is as an injective function $"Fin" w -> "Fin" n$.
// 
We refer to this as a partial permutation --- one can view it as the first $w$ digits in an $n$-permutation.
// 
In the semantics, it is _completed_ to form a full permutation, and then used to shuffle the qubits for the gates as required.
// 
In practise, it is useful to wrap these details up into their own inductive type, and then use this as the shape of the feature container.

= Modular Semantics

Now that we have defined our syntax, we turn to giving the language a semantics.
// 
A key insight is that this we can reformulate this question as giving a model for an $F$-algebra.


There is a close connection between containers and universal algebra.
// 
A container can essentially be seen as defining the signature of a single-kinded algebra.
// 
The shapes of the container are the operators of the signature, and the position function gives the arities.
// 
Extension is a functor, which we can use to form an $F$-algebra.
// 
The idea is that we can see extensions into $X$ as expressions over $X$. 
// 
The functor lets us form syntax over some set of base values.
// 
The syntax is shallow --- only one layer deep.


A (model for an) $F$-algebra over an endofunctor $F : cal(C) -> cal(C)$ is comprised of two things. 
// 
Firstly, $A : cal(C)$ an object of $cal(C)$, called the _carrier._
// 
Secondly, a morphism $alpha : F A -> A$ called the action, which takes expressions over $A$ ($F A$) to their values in $A$.
// 
The idea is that $alpha$ defines how to _evaluate_ expressions when we know how to evaluate the sub-parts.
// 
When it exists, the least fixed point of the functor ($mu F$) always has an $F$-algebra structure.
//
This is easy to see; by definition there is an isomorphism $F (mu F) iso mu F$.
// 
We can take the left-to-right direction of this isomorphism to get an action for the algebra:


$ "in" : F (mu F) -> mu F $ 

This is called the _initial algebra_ of $F$.
// 
It is initial because for any other model ($alpha : F A -> A$), there is a unique homomorphism $"fold"_alpha$ between the initial algebra and the model.

#figure(caption: [Universal property of the initial algebra of a functor])[
  #fl.diagram($
    F (mu F) 
      hom("d", ->, label: F ("fold"_alpha)) 
      hom("r", ->, label: "in") 
    & mu F hom("d", ->, label:"fold"_alpha, label-side: #right)\ 
    F A hom("r", ->, label: alpha)
    & A
  $)
]

The function $"fold"_alpha : mu F -> A$ is exactly what we need to define a denotational semantics in $A$ for the AST. 
// 
Equivalently, we can view $"fold"$ as a higher order function:
$
  "fold" : (F A -> A) -> mu F -> A 
$

Intuitively, fold first evaluates the children --- applying fold recursively to each child in `ch`.
// 
This produces an extension into $A$, which can in turn be evaluated directly using $alpha$.
== Coproduct Models 

Now, we turn to compositionality of semantics. 
// 
We would like to be able to give semantics to our features individually, and derive the semantics of coproducts.
//
A coproduct model allows us to do just this.
// 
Given two containers $F, G$, each having a model in $A$, $alpha : F A -> A$, $beta : G A -> A$, we can take their coproduct to yield a model for the coproduct of the containers:
// 
$
  iota[alpha, beta] : (F ":+:" G) A -> A 
$
// 
We refer to $iota[alpha, beta]$ as the coproduct model of $alpha$ and $beta$.
// 
The coproduct model is easy to define.
// 
First, note the following natural isomorphism between the functors $F plus.o G$ and $X -> F X plus.o G X$:
$
  iota_A : (F ":+:" G) A iso F A plus.o G A
$
// 
The coproduct model can then be seen simply as the relevant component of $iota$ composed with the copairing of $alpha$ and $beta$:
// 
$
  iota[alpha, beta] = [alpha, beta] compose iota
$

= Subsumption

With a methods for defining the syntax and semantics of languages fixed, we can turn to showing that some of our intuitions hold.

One language subsumes another if it is at least as expressive.
// 
i.e. B subsumes A if everything in A can be written in B.
// 
To formalise this idea, we introduce "Semantics preserving functions".
// 
Let $L, M$ be two languages with semantics in the same domain $cal(X)$.
// 
Let the semantic functions be $alpha[|-|] : L -> cal(X)$ and $beta[|-|] : M -> cal(X)$.
// 
A function $f : L -> M$ is semantics preserving if for all programs, the semantics remains the same:
$
  forall p : L, alpha[|p|] = beta [|f (p)|]
$

Equivalently, we may represent this as a diagram:

#figure()[
  #fl.diagram($\
  L hom("rr", f, "->") hom("dr", alpha, "->") && M hom("dl", beta, "->") \
  & cal(X)
  $)
]

$L$ is subsumed by $M$ (written $L prec.eq M$) if there exists such a function from $L -> M$.
// 
Furthermore, we use this notation to denote the type of semantics preserving functions --- i.e. $f : L prec.eq M$.
// 
When there are semantic preserving functions in both directions, the languages are isomorphic with respect to their semantics in the relevant domain.
// 
If there exists only a function in one direction, then the subsumption is _strict._ 
// 
For this, we write $L prec M$.
// 
The intuition for this is that there are program that can be written in $M$ that cannot be expressed in $L$.


The identity function always forms a SPF from a language to itself.
// 
SPFs can be composed to form new semantic preserving functions, using the regular composition of functions.
// 
From this, we obtain also that this composition is associative.
// 
Thus, languages and semantic preserving functions form a category.
// 
This is exactly the slice category over the domain $cal(C)_(\/cal(X))$.
// 
We should note that an isomorphism of languages with respect to their semantics in $cal(X)$ does not imply an isomorphism in $cal(C)_(\/cal(X))$.
// 
Isomorphisms in $cal(C)_(\/cal(X))$ represent essentially syntactic isomorphisms --- i.e. translations from one language to another and back such that exactly the same term is recovered.
// 
This is apparent when one considers that isomorphisms in a slice category imply an isomorphism in the base category.
// 
To obtain a category where semantic isomorphisms are true isomorphisms, we would need to quotient the objects, such that the only endomorphism for any object is the identity morphism.
// 
The elements of objects representing languages in this setting would be equivalence classes of programs.


== Embedding & Canonical forms for Modular Syntax

This is enough to now show several interesting facts, regarding the coproducts of features.
// 
Let $A,B$ be containers, with semantics in the same domain (say $alpha : A X -> X$ and $beta : B X -> X$).
// 
Whenever we take a coproduct, let us assume that the semantics of the result is given by the standard model coproduct defined in section 3.
// 
Given this data, the following subsumption functions are defined:

#figure[$
    (1) && "fold" "inl" &: mu A prec.eq mu (A plus.o B)\
    (2) && "fold" [id, id] &:mu (A plus.o A) prec.eq mu A \
    (3) &&  "fold" ["inr", "inl"] &: mu (A plus.o B) prec.eq mu (B plus.o A)
$]



(1) shows that semantic subsumption also captures syntactic subsumption, so long as the languages have semantics in the same terms.
// 
By specialising to (1) with $B=A$, and then taking (2), we get $A plus.o A tilde.equiv A$.
// 
(3) gives $A plus.o B tilde.equiv B plus.o A$.
// 
This gives a normal form for feature sets; distinct features only, lexicographic ordering.

= Semantic Strength

In order to discuss semantic subsumption, we required that all the features had semantics in the same terms.
// 
However, the initial motivation of this paper was to exploit the benefits of working in different semantic domains.
// 
Thus, we need some way to deal with different semantic domains in a coherent way.
// 
To do this, consider again the two semantics we presented earlier in section 1.
// 
Given a semantics in gates, we can produce a CPTP map:
// 
$ 
  "CPTP"[|p|] = lambda rho . G[|p|] rho G[|p|]^dagger
$
// 
We can formulate this as a function,
// 
$
  e : "Gate" n -> "CPTP" n
$
// 
and rewrite our CPTP semantics as:
// 
$
  "CPTP"[|-|] = e compose G[|-|]
$


The CPTP semantics are in some sense derivable from the gate semantics;
thus we say that gate semantics are _weaker_ than the CPTP semantics.

Not just any function will do for this $e$. 
// 
We would like for there to be _no loss of information_ when converting from a weaker domain to a stronger one. 
// 
This is motivated by intuition; we should not loose information when we add the capability to model measurement.
// 
For this reason, we require that $e$ should be an _embedding._
// 
This means that $e$ has a one-sided inverse, which we call $p$ (for 'projection'). 


Given a pair of semantic domains $cal(X), cal(Y)$, a pair $(e,p)$ are a suitable witness to the fact that $cal(X)$ is weaker than $cal(Y)$ (written $(e,p) : cal(X) isWeakerThan.eq cal(Y)$) when:
$
  e : cal(X) -> cal(Y) \
  p : cal(Y) -> cal(X) \
  p compose e = id_cal(X)
$



Gates and choi matrices are not in fact a suitable pair. 
// 
This is because although gates cleanly embed into choi matrices, the embedding function is not injective.
// 
Gates which differ only by a global phase are mapped to the same choi matrix. 
// 
This is not a problem, as it captures an important physical fact.
// 
However, it does mean that we in fact need to work with gates quotient global phase.



== Model Compatibility 

Given that one domain is weaker than another ($(e,p) : cal(X) isWeakerThan.eq cal(Y)$), what does it mean for two models ($alpha : F cal(X) -> cal(X)$, $beta : F cal(Y) -> cal(Y)$) to respect this relation?
// 
We would like to be able to write $"fold" beta = e compose "fold" alpha$,
as this is what allows us to lift equality judgements from $cal(X)$ to $cal(Y)$.

This is possible when $e$ forms an algebra homomorphism between $alpha$ and $beta$.
// 
That is to say, the following diagram commutes:
// 
#figure()[
  #fl.diagram($
      F cal(X) hom("d", "->", alpha) 
        hom("r", "->", label: F e) 
    & F cal(Y) hom("d", "->", beta)\
      cal(X) 
        hom("r", "->", label: e)
    & cal(Y)
  $)
]

This is sufficient to show that $e$ forms the desired relation between the two folds.
//
This follows from the initiality of $mu F, "in"$ and the universal property of $"fold"$.
//
To see this, we consider the larger diagram in @hom_etc.
// 
First, note that the outer square and leftmost cell commute by the definition of the initial algebra.
// 
$"fold" alpha$ and $"fold" beta$ form algebra homomorphisms between the initial algebra and $alpha$ and $beta$ respectively.
// 
We take as given that the rightmost cell commutes --- that is, that $e$ is an algebra homomorphism between $alpha$ and $beta$.
// 
This gives us a second algebra homomorphism from $"in"$ algebra to $beta$.
// 
But since $"in"$ is initial, this homomorphism must be equal to the canonical $"fold" beta$.
// 
Thus we have that $"fold" beta = e compose "fold" alpha$.

#figure(caption: [Diagram that is hard to caption])[
  #fl.diagram($
    F (mu F)
        hom("rr", "->", F ("fold" beta))
        hom("dr", "->", label: F ("fold" alpha))
        hom("ddd", "->", label: "in")
      && F cal(Y) 
        hom("dl", "<-", label: F e, label-side: #right)
        hom("ddd", "->", beta)
      \
    & F cal(X)
      hom("d", "->", alpha)
      \
    & cal(X) \
    mu F 
      hom("ur", "-->", "fold" alpha)
      hom("rr", "-->", "fold" beta)
    && cal(Y)
      hom("ul", "<-", e)
  $)
]<hom_etc>



== Deriving Semantics 

Given a pair of semantic domains $cal(X), cal(Y)$, where one is weaker than the other $(e, p) : cal(X) isWeakerThan.eq cal(Y)$ and a model in one of these, we might like to be able to synthesise a compatible model in the other.
// 
In general, this is not possible.
// 
In this section, we will present why not.


=== From Stronger to Weaker 

Given a model in the stronger domain $beta : F cal(Y) -> cal(Y)$, it is possible to derive a model in the weaker domain, simply by composition of functions:
// 
#figure()[
  #fl.diagram($
      F cal(X) hom("d", "-->", alpha) 
        hom("r", "->", label: F e) 
    & F cal(Y) hom("d", "->", beta)\
      cal(X) 
        hom("r", "<-", label: p)
    & cal(Y)
  $)
]

However, this definition is not particularly useful to us in practice.
// 
There are two things to note here.
// 
Firstly, this model is not properly compatible.
// 
While $p$ forms a homomorphism between $cal(Y)$ and $cal(X)$, 
we do not get any guarantee that $e$ forms a homomorphism in the opposite direction.
// 
Thus, this model does not properly support the reasoning we wish to do.

Even when this is the case however, 
// 
This model essentially represents first converting the syntax to the complex domain, evaluating the expression there, and then moving back to the simple one.
// 
In other words, it represents moving to the more complex domain in order to do all the computation.
// 
This runs directly contrary to our initial motivation; the hope was that by working in a simpler domain, we could gain some computational advantage.
// 
Thus, if possible, we would like to have a _native_ model in $cal(X)$ which does not require casting through $cal(Y)$.

=== From Weaker to Stronger

The same construction can be performed in the opposite direction, but this presents its own set of issues.
// 
This corresponds to project from $cal(Y)$ into $cal(X)$. 
// 
However, we have no guarantees about information retention in this direction.
// 
Essentially, if $cal(Y)$ contains any additional structure when compared to $cal(X)$, then it is all erased by this projection.


We might hope that we could in some sense extend $alpha$ to cover the elements of $cal(Y)$ not in the image of $cal(X)$ under $e$.
// 
In other words, there is no single model $beta$ which uniquely completes this diagram.
//
And we have little hope of choosing the right $beta$ from the collection.
// 
The 'free' model

#figure[
  #fl.diagram($
      F cal(X) hom("d", "->", alpha) 
        hom("r", "<-", label: F p)
    & F cal(Y) hom("d", "-->", beta)\
      cal(X) 
        hom("r", "->", label: e) 
    & cal(Y)
  $)
]

There are two cases where this construction does yield a sensible model.
// 
Firstly, when $(e,p)$ form a pair of _true_ inverses; that is when $e compose p = id_cal(Y)$. 
// 
In this case however, $e, p$ form an isomorphism between $cal(X)$ and $cal(Y)$.
//
Therefore, $cal(X)$ is not any simpler than $cal(Y)$.

The second case where this construction yields a sensible model is when the functor $F$ itself is invariant under $X$.
// 
This corresponds exactly to the terminal features.
// 
These you can think of as picking out constants in the relevant domain.
// 
It is possible to take the value one of these constants in $cal(X)$  and use $e$ to choose the corresponding value in $cal(Y)$.

== Coproduct Models

- model coproduct preserves compatibility
- Not because it's functorial
- model coproduct is not a functor
  - At least, not in any obvious way
  - Really, its a kind of copairing = universal morphism
  $->$ Is it a coproduct in the slice?
$cal(C)_(\/A)$


#bibliography("refs.bib")