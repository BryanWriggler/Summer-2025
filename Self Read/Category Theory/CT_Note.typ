#import "@preview/rubber-article:0.4.1": *
#import "@preview/ergo:0.1.0": *
#import "@preview/fletcher:0.5.5" as fletcher: *

//basic template setup
#show: article.with(
  header-display: true,
  eq-numbering: "(1.1)",
  eq-chapterwise: true,
  margins: 1.0in,
)
#show: ergo-init.with(
    colors: "bootstrap",  
    headers: "classic", //"tab" for upper bar, classic for the one I used, sidebar for the emphasis on the left
    all-breakable: true,
    inline-qed: true
)


//common syntaxes needed
#let neq = $"!="$
//analysis 
#let Vol = $"Vol"$
//algebra
#let Hom = $"Hom"$
#let End = $"End"$
#let Aut = $"Aut"$
#let Coker = $"Coker"$
#let Gal = $"Gal"$
#let Nil = $"Nil"$
#let char = $"char"$
#let Id = $"Id"$
//complex 
#let Real = $"Re"$
#let Imag = $"Im"$ //also used for image
#let Arg = $"Arg"$
#let Res = $"Res"$
//lie algebra
#let gl = $frak("gl")$
#let sl = $frak("sl")$
#let sp = $frak("sp")$
//category theory
#let Ob = $"Ob"$ //object of category
#let Mor = $"Mor"$ //morphisms of objects


//start document
#maketitle(
  title: "Typst Template",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

= Basics of Category Theory
It's a study of structures, in contrast to the study of sets. So, it's build upon the relations between collections of "objects" with similar structures, rather than the meaning of each individual sets.

#defn[Category][
  $cal(A)$ is a category, which consists of a collection of objects (normally a #emph("Class") of objects), and morphisms in between the objects satisfying some rules.

  More precisely, it consists of a class of objects $Ob(cal(A))$, such that for every two objects $A,B,C,D$ of $cal(A)$, there exists a set of morphisms, denoted as $Mor_cal(A)(A,B)$ or $Hom_cal(A)(A,B)$, that satisfies the following:
  + #text(weight:"bold")[Law of compositions:] There exists composition map $compose : Mor_cal(A)(B,C) times Mor_cal(A)(A,B) arrow.r Mor_cal(A)(A,C)$, where for every $f in Mor_(A)(A,B)$ and $g in Mor_(A)(B,C)$, we have $(g,f) arrow.r.bar g compose f$ (or denoted as $g f$). 

    Furthermore, the law of composition is #text(weight: "bold")[associative]. Which, for every $f in Mor_cal(A)(A,B)$, $g in Mor_cal(A)(B,C)$, and $h in Mor_cal(A)(C,D)$, we have $(h compose g) compose f = h compose (g compose f) in Mor_cal(A)(A,D)$.

  + #text(weight: "bold")[Existence of Identity:] There exists a morphism $Id_A in Mor_cal(A)(A) := Mor_cal(A)(A,A)$, that acts like an identity of $A$ (which serves as a right or left identity of $Mor_cal(A)(A,B)$ and $Mor_cal(A)(B,A)$ respectively). Which, for every $f in Mor_cal(A)(A,B)$ and $g in Mor_cal(A)(B,A)$, we have:
    $ f compose Id_A = f in Mor_cal(A)(A,B),quad Id_A compose g = g in Mor_cal(A)(B,A) $

  + #text(weight: "bold")[Disjoint Morphisms:] Given $Mor_cal(A)(A,B), Mor_cal(A)(C,D)$, they're disjoint unless $A=B$ and $C=D$
]
#example[Category of sets][
  Let $cal(S)$ be the category of sets, while the morphisms being set functions. Then, between any sets there exists a collection of functions between the two sets. Every set has an identity to itself that serve as left / right identity for any other set of morphisms, and two collections of set functions are disjoint unless the domain and codomain matches up.
]
For notation purposes, we denote $Mor_cal(A)(A,B)$ as just $Mor(A,B)$ if the category is clear; and, we call the set of morphisms #text(weight: "bold")[Endomorphisms] if it's toward the same object, denotes as $End_cal(A)(A) := Mor_cal(A)(A,A)$.

Moreover, for simplicity purpose, people also use arrows (like in set functions) to replace $Mor(A,B)$ notation: For instance, $f in Mor(A,B)$ is denoted using $f:A arrow.r B$ instead.

#example[Category of Relations][
  Let $S$ be a set with relation $tilde$ that is both reflexive and transitive. For every $a,b in S$, define $Mor(a,b) = {(a,b)} in S times S$ if $a tilde b$, and $Mor(a,b)=emptyset$ otherwise.

  Then, since the relation is reflexive, then $a tilde a$ for all $a in S$, hence $Id_a = (a,a)$ exists; then, if $a tilde b$ and $b tilde c$, we have $a tilde c$ baesd on transitive property, hence for $(a,b) in Mor(a,b)$ and $(b,c) in Mor(b,c)$, we have $(b,c) compose (a,b) = (a,c)$.

  This composition is associative because of the transitive property also.

  Finally, since the relation is reflexive, $Id_a:=(a,a) in Hom(a,a)$.
]
Which, a specific example of the above is a category on a POset $(S,<=)$, since it's both reflexive and transitive.

#example[Category of Specific Objects (Diagrams into specific objects)][
  Given $C$ a category, any object $A in Ob(C)$, define a category $C_A$, where $Ob(C_A)$ collects all morphisms $f:Z arrow.r A$ for some other object $Z in Ob(C)$.

  Then, to define the morphisms, given $f,g in Ob(C_A)$ (where $f:Z_1 arrow.r A$ and $g:Z_2 arrow.r A$), define $Hom_{C_A}(f,g) := {h in Hom_C (Z_1,Z_2) | f = g compose h}$, which is the set of morphisms $h$ satisfies the following commutative diagram:

    #diagram(cell-size: 30mm, $
	    Z_1 edge(h, "->") edge("d", f, ->) & Z_2
      edge("dl", g, "->")\ A
      
      $)

  Which, given any $f in Ob(C_A)$, since $f:Z arrow.r A$, then $Hom_(C_A)(f,f)$ contains $Id_Z$ (since $f = f compose Id_Z$), so the identity is satisfied. Diagramatically, we have:

  #diagram(cell-size: 30mm, $
      Z edge("r", Id_Z, ->) edge("d", f, ->) & Z edge("dl", f, ->)\ 
      A
      $)


  Now, suppose $k in Hom_(C_A)(f,g)$ and $l in Hom_(C_A)(g,h)$, we have the following diagram:
  #diagram(cell-size: 30mm, $
	    Z_1 edge(k, "->") edge("d", f, ->) & Z_2 edge("dl",g,->) edge("r",l,->) & Z_3
      edge("dll", h, "->")\ A
      $) 

  Since this diagram commutes, then we have $h compose (l compose k) = f$, hence $l compose k in Hom_(C_A)(f,h)$. Which, associativity follows from that.
]

#example[Category of Power sets][
  Given $S$ a set, define category $hat(S)$ with $Ob(hat(S)) = cal(P)(S)$ (the power set of $S$). Then, for any $A,B$ that are objects of $hat(S)$ (namely $A,B subset.eq S$), define $Hom_hat(S)(A,B)$ to be the pair $(A,B)$ if $A subset.eq B$, and it being empty set otherwise. Which, if we use $subset.eq$ as the partial order on the set $Ob(hat(S))$, this is the same as the#text(weight: "bold")[Category of Relations] (with reflexive / transitive property).

  Then, for every object $A$, since $A subset.eq A$, we have the pair $(A,A) in End_hat(S)(A)$ as the identity.

  Composition $(A,B) in Hom(A,B)$ and $(B,C) in Hom(B,C)$ has $(A,C) in Hom(A,C)$ (since $A subset.eq B subset.eq C$).
]

#example[Category of Relations + specific objects][
  Given set $ZZ$ as the initial category $C$ and the relation $<=$, which for every $m,n in ZZ$, we have $Hom(m,n) = {(m,n)}$ iff $m <= =n$ (and $emptyset$ otherwise). Now, let $A = 3$, then the category $C_A$ consists of all the morphisms $(m,3)$ (which $m <= 3$ by definition). 

  Which, the morphisms in category $C_A$  are the ones that has an intermediate morphism, i.e. given $(m,3)$ and $(n,3)$ that has nonempty morphisms from the first to the second, we have the following relations:

  #diagram(
    cell-size: 30mm,
    $m edge((m,n), "->") edge("d", (m,3), ->) & n
      edge("dl", (n,3), "->")\ 3$
  )

  Which can only happen iff $m\leq n$ (i.e. there's morphism between $m,n$ in the original category).
]

= Another approach to define Category:
#definition[Category 2][
  A category $C$ is defined to be a class of "morphisms", together with functions $S,T:C times C arrow.r C$ (called "source" and "target") and partial function $compose: C times C arrow.r C$ (called "composition"), such that the following axioms are true for all $f,g in C$:
  + $S(f) = S(S(f)) = T(S(f))$ (i.e. given $f:A arrow.r B$, $S(f):A arrow.r A$)
  + $T(f)=T(T(f)) = S(T(f))$ (i.e. $T(f):B arrow.r B$)
  + $g compose f$ is defined iff $S(g) = T(f)$ (i.e. $g compose f$ makes sense, iff $f:A arrow.r B$ and $g:B arrow.r C$, while the circulation map on $B$ in between is the same, so the diagram in general has no ambiguity).
  + $S(g compose f) = S(f)$, and $T(g compose f) = T(g)$.
  + $f compose S(f) = f$, and $T(f) compose f = f$ (intended for $S(f) = Id_A$ and $T(f) = Id_B$).
  + $compose$ is associative, if multiple composition happens.


  Try and verify this creates an equivalent definition with the old one (Hint: Take $Ob(C) := Imag(S) = Imag(T)$ to start with).
]

= Morphisms:
#definition[Isomorphisms][
  A morphism $f in Hom(A,B)$ is said to be an isomorphism, if there exists $g in Hom(B,A)$, such that $g compose f = Id_A$ and $f compose g = Id_B$.
]
Which, the inverse is unique, since suppose $g, h in Hom(B,A)$ both serve as an inverse of $f$, we get $g = Id_A compose g = (h compose f) compose g.= h compose (f compose g) = h compose Id_B = h$. Hence, we can denote $f^(-1) := g$ (since it is unique).

#prop[
  + Each identity $Id_A$ is an isomorphism, and is its own inverse.
  + If $f$ is an isomorphism, then $f^(-1)$ is an isomorphism, and $(f^(-1))^(-1) = f$.
  + If $f in Hom(A,B)$, $g in Hom(B,C)$ are isomorphisms, then $(g compose f)^(-1) = f^(-1) compose g^(-1)$ 
][
  1. Since $Id_A compose Id_A = Id_A$, we have $Id_A = (Id_A)^(-1)$.
  2. Let $g = f^(-1) in Hom(B,A)$, then $f$ satisfies $f compose g = Id_B$ while $g compose f = Id_A$, hence $g$ is an isomorphism, with $f$ being its inverse. So, $(f^(-1))^(-1) = g^(-1) = f$.
  3. Since $(g compose f) compose (f^(-1) compose g^(-1)) = g compose Id_B compose g^(-1) = Id_C$, multiply $(g compose f)^(-1)$ on the left provides the desiredresult.
]
Which, if we consider a set of isomorphisms going from an object to itself, we call "automorphisms", and denote as $Aut(A)$.

Notice that $Id_A in Aut(A)$, if $f in Aut(A)$ we have $f^(-1) in Aut(A)$, and the composition on $Aut(A)$ is associative, which forms a group regardless of the category (as long as the category is "small", or the collection of morphisms between any two objects are sets).

#definition[Monomorphisms and Epimorphisms][
  Given $C$ a category. 
  
  A morphism $f in Hom_C (A,B)$ is a #text(weight: "bold")[Monomorphism], if for any object $Z$ of $C$ and all morphisms $g_1,g_2 in Hom_C (Z,A)$:
  $ f compose g_1 = f compose g_2 ==> g_1=g_2 $
  Which, monomorphisms are "left cancellative".

  \ 

  Similarly, $f$ is an #text(weight: "bold")[Epimorphism], if for any object $Z$ of $C$ and all morphisms $h_1,h_2 in Hom_C (B,Z)$:
  $ h_1 compose f = h_2 compose f ==> h_1 = h_2 $
  Which, it is "right cancellative".
]
#example[Monomorphisms and Epimorphisms over Sets][
  In the category of sets, monomorphisms and epimorphisms are precisely the injective and surjective functions.

  \ 

  Monomorphisms:
  1. $==>:$ Suppose $f:A arrow.r B$ is an injective set function, then for any other set $Z$ and any morphisms $g_1,g_2:Z arrow.r A$, suppose $f compose g_1 = f compose g_2$, then for all $z in Z$, we have $f(g_1(z))=f(g_2(z))$, which by injectivity, $g_1(z)=g_2(z)$, hence $g_1=g_2$.

  2. $<==:$ Suppose $f:A arrow.r B$ is a monomorphism, then for any set $Z$ and any morphisms $g_1,_2:Z arrow.r A$, $f compose g_1 = f compose g_2$ implies $g_1=g_2$.
    Which, suppose for any $x,y in A$ satisfying $f(x)=f(y)$, consider $Z = {a}$ and the map $g_1,g_2: arrow.r A$ by $g_1(a)=x$ and $g_2(a)=y$. Which, notice that $f compose g_1(a) = f(x) = f(y) = f compose g_2(a)$, then $f compose g_1 = f compose g_2$, showing that $g_1 = g_2$ by assumption. Hence, we must have $x=g_1(a)=g_2(a)=y$, proving that $f$ is injective.

  \ 

  Epimorphisms:
  1. $-->:$ Suppose $f:A arrow.r B$ is a surjective set function, then for any other set $Z$ and any morhpisms $h_1,h_2:B arrow.r Z$, suppose $h_1 compose f = h_2 compose f$, then for all $b in B$, by surjectivity there exists $a in A$ satisfying $f(a) = b$. Hence, $h_1(b) = h_1 compose f(a) = h_2 compose f(a) = h_2(b)$, showing that $h_1=h_2$. So, $f$ is an epimorphism.

  2. $<==:$ We'll prove the contrapositive. Suppose $f:A arrow.r B$ is not surjective. Then, take $Z = B union {c}$ for simplicity (where can choose $c$ such that $c in.not B$), we have $i:B arrow.r.hook B union {c}$. Since $f$ is not surjective, there exists $b in B \\ f(A)$. Then, define $h:B arrow.r B union {c}$ by $h(x) = x$ (if $x != b$) and $h(b) = c$, then since $c=h(b)!= b = i(b)$, we have $h!= i$. However, for all $a in A$, since $f(a) != b$, then we have $i(f(a)) = f(a)=h(f(a))$, hence $i compose f = h compose f$. This is a counterexaple to the statement of being an epimorphism.
]

= Universal Properties
#definition[Initial / Final Objects][
  Given $C$ a category. An object $I$ of $C$ is #text(weight: "bold")[Initial] in $C$, if for all object $A$ of $C$, there exists #text(weight: "bold")[precisely one] morphism $I arrow.r A$ in $C$ (i.e. $Hom_C (I,A)$ is singleton).

  Similarly, an object $F$ of $C$ is #text(weight: "bold")[Final] in $C$, if for all object $A$ of $C$, there exists #text(weight: "bold")[precisely one] morphism $A arrow.r F$ in $C$.
]
#example[Category with no Initial or Final Objects][
  Given $ZZ$ as the category, with objects being integers, and morphisms induced by the partial order $<=$, then there's no elemnt with exactly one morphism with all other elements.

  In contrast, if we define the slice category $ZZ\/3$, then $(3,3)$ is the final object (since for every other morphism $(n,3)$ that is contained as an object of $ZZ\/3$, we must have $n<= 3$, hence $(n,3)$ is acting precisely as a morphism from $(n,3)$ to $(3,3)$).
]
#example[Unique / Non-uniqueness of Initial or Final Objects][
  #text(weight: "bold")[Unique case:]
  In category of sets, $emptyset$ acts as an initial object (since for any nonempty set $A$, there exists precisely a function $f:emptyset arrow.r A$, namely the null function), while a function $f:emptyset arrow.r emptyset$ can also be defined. This is unique, because for any nonempty set $A$, one can always pick a set with at least $2$ element (say $B$), then there are more than one functions $f:A arrow.r B$, showing $A$ can't be an initial object.
]

