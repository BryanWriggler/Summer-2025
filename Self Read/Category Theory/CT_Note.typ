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
  title: "Category Theory",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

#outline(
  title: [Table of Contents]
)

#text(weight: "bold")[Note:] This document is for my personal understanding, so there are quite some jumps between contents (which it's mostly based on Aluffi and the Summer Project 2025 done in CCS UCSB).

\ 

\ 

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

#pagebreak()

= Another approach to define Category: (Not done)
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

#pagebreak()

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

#pagebreak()

= Universal Properties (Loose)
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

  #text(weight: "bold")[Non-unique case:] Again, in category of sets, any singleton ${*}$ is a final object, since for every other nonempty set $A$, there exists exactly one function $f:A arrow.r {*}$, namely the constant function. However, since one can create as many singletons as they wish, this final object is clearly not unique (yet unique up to isomorphism).
]
#prop[Given $C$ as a category. 
- If $I_1,I_2$ are both initial objects in $C$, then $I_1 tilde.equiv I_2$.
- If $F_1,F_2$ are both final objects in $C$, then $F_1 tilde.equiv F_2$.

Furthermore, these isomorphisms are uniquely determined.][
  - For $I_1, I_2$ that are both initial, there exists precisely one morphism $f_1:I_1 arrow.r I_2$ and $f_2:I_2 arrow.r I_1$, showing that $f_2 compose f_1:I_1 arrow.r I_1$ is an endomorphism on $I_1$. Since there also exists precisly one endomorphism on $I_1$ by definition of initial object, namely $Id_(I_1)$, then we must have $f_1 compose f_1=Id_(I_1)$. Similarly, we must have $f_1 compose f_2:I_2 arrow.r I_2$ being precisely $Id_(I_2)$, showing that $I_1, I_2$ are isomorphic, with the isomorphism uniquely determined by $f_1, f_2$.

  - For $F_1,f_2$ that are both final, again there exists precisely one morphism $g_1:F_1 arrow.r F_2$ and $g_2:F_2 arrow.r F_1$. Which, based on the fact that $F_1,F_2$ can each have precisely one endomorphism based on the property of final objects (namely the identity on themselves), we must have $g_1 compose g_2:F_2 arrow.r F_2$ be $Id_(F_2)$, and $g_2 compose g_1: F_1 arrow.r F_1$ be $Id_(F_1)$, showing that $F_1,F_2$ are isomorphic, and with isomorphism determined by $g_1,g_2$.
]

\ 

When talking about universal properties, we need functors. But, a vague idea can be stated as follow: A construction satisfies #emph[Universal Property] (or, "the solution to a universal problem") when it may be viewed as a terminal (final) object of a category. Which, a lot of the time the context of the category is explained purely by words (about their property), and hardly mention "category" of its structure. (For instance, when talking about quotients based on an equivalence relation).

A common (yet more complicated) pattern is "An object $X$ is universal with respect to the following property: "For any object $Y$ such that [statement 1], there exists a unique morphism $Y arrow.r X$ such that [statement 2]". The reason why using $Y arrow.r X$ is because we want to classify $X$ as a terminal object of the category.

#example[Quotient of Sets][
  Given a set $A$ together with an equivalence relation $tilde$, the quotient $A\/tilde={[a]_tilde | [a]_tilde = [b]_tilde <==> a tilde b}$ is the construction of the quotient of $A$, based on equivalence relation $b$.

  Here, we want to claim "#emph[The quotient $A\/tilde$ is universal with respect to the property of, mapping $A$ to a set in such a way that equivalent elements have the same image]". In other words, we want to talk about all the functions $phi:A arrow.r Z$, such that $a tilde b ==> phi(a)=phi(b)$ (where $Z$ is an arbitrary set).

  Which, a category we can consider is the collection of all the pairs ($phi, Z$) (which can just be determined using $phi$), with morphisms being the functions that forms a commutative diagram with the two functions. I.e., given $phi_1:A arrow.r Z_1$ and $phi_2:A arrow.r Z_2$, if $h in Hom(phi_1,phi_2)$, we get:

  #diagram($
              & A edge("dl", phi_1, ->) edge("dr", phi_2, ->) \ 
              Z_1 edge("rr", h, ->)& & Z_2
           $)

  \ 

  In this case, to find the object satisfying the universal propecty, is the same as saying "the function can be factored through $A\/ tilde$", so the goal is to prove that $pi:A arrow.r A\/tilde$ is the initial object in this category. 

  \ 

  The reason it's an initial object, is because for any function $phi:A arrow.r Z$ satisfying the given property, we can define $overline(phi):A\/tilde arrow.r Z$ by $overline(phi)([a]_tilde) = phi(a)$, since for all $a tilde b$, we have $phi(a)=phi(b)$ and $[a]_tilde = [b]_tilde$, hence this map is well-defined. And, the following commutative diagram is true:

  #diagram($
             A edge("rr", phi, ->) edge("dr", pi, ->) && Z\
            & A\/ tilde edge("ur", overline(phi), ->)
           $)

  Uniqueness is clearly true, due to the fact that the two quotient maps $A\/tilde arrow.r Z$ must agree on every element. So, $pi:A arrow.r A\/tilde$ is an initial object (which in its opposite category is a final object), hence it satisfies what we want for the universal property.
]

#example[Products of Sets][
  For naive set theory, any two set $X,Y$ has product $X times Y$ formed by ordered pairs ${(x,y) | x in X, y in Y}$. However, based on the quotients from before, we know $pi_x:X times Y arrow.r X$ and $pi_y:X times Y arrow.r Y$ that projects to the given element in the pair are uniquely determined projection maps. Then, for any set $Z$, if we have maps $phi_1:Z arrow.r X$ and $phi_2:Z arrow.r Y$, since $phi_1(z) in X$ and $phi_2(y) in Y$ for all $z in Z$, we can define a map $sigma:Z arrow.r X times Y$ by $sigma(z)=(phi_1(z),phi_2(z))$ which is well-defined (since $phi_1(z),phi_2(z)$ are unique according to input $z$, which is a property of functions).

  Notice that under this construction, the following diagram commutes:

  #diagram($
             & Z edge("dl", phi_1, ->) edge("dr", phi_2, ->) edge("d", sigma, ->) \ 
             x & X times Y edge("l", pi_x, ->) edge("r", pi_y, ->) & Y
           $)
  
  Then, we can claim that "for every set $Z$ and morphisms $phi_1:Z arrow.r X$, $phi_2:Z arrow.r Y$, there exists a unique morphism $sigma:Z arrow.r X times Y$ such that the above diagram commutes", which the pair $(pi_x,pi_y)$ can be viewed as a final object of the category (if using any pair $(phi_1,phi_2)$ as object, and $sigma$ with the above diagram commuting being morphisms, hwere $X times Y$ now becomes arbitrary set with a pair of functions described above).

  As a side note, the map $sigma$ is also denoted as $phi_1 times phi_2$, since it can also be viewed as having the two functions acting on their corresponding coordinate.
]

A small note here is that $X times Y$ can be swapped by $X' times Y'$, where $X' tilde.equiv X$ and $Y' tilde.equiv Y$, so in the category of sets, product is not "unique" as object, but rather unique up to isomorphism.

\ 

Notice that the above $X times Y$ can actually be phrased in other categories (by viewing the pair of "projections" $pi_x$ and $pi_y$ as final object in the category of pairs of morphisms, one with target $X$ and the other with target $Y$). So, with more precise definition about universal properties (and what categories are chosen), products can be generalized to not just sets.

Which, we say a category $C$ #emph[has (finite) products] (or #emph[with (finite) products]), if for any objects $A,B$ in $C$, the category $C_(A,B)$ has  final objects (which is the category of objects being pairs of morphisms $(phi_1,phi_2)$ with $phi_1:Z arrow.r A$ and $phi_2:Z arrow.r B$, and morphisms being $h:Z_1 arrow.r Z_2$ if the first pair has source $Z_1$, the second pair has source $Z_2$ while the diagram commutes).
Since final objects are not necessarily unique, there might be more than one products.

#example[Products in category $(ZZ, <=)$][
  Given any integer $a,b in ZZ$, for any $c in ZZ$ with morphism $Hom(c,a)$ and $Hom(c,b)$ being nonempty (which implies $c<= a,b$), the only pair of morphisms $c arrow.r a$ and $c arrow.r b$ we can find are $(c,a)$ and $(c,b)$ respectively. Which, can be given as the following digram:

  #diagram($
             & c edge("dl", (c,a), ->) edge("dr",(c,b),->)\
            a && b
           $)

  If we want to factor the morphisms through some objects in $(ZZ,<=)$, then this object $n$ better have morphisms to $a$ and $b$, or $n<= a,b$; on the other hand, we want all $c <= a,b$ to have morphism to $n$, so we also need $c<= n$. Then, the only possible choice is $n=min{b,c}$.

  Which, notice that it satisfies all the given properties: For any $c$ with $c<=a,b$, we must have $c <= min{b,c} <= b,c$, so the morphisms $(c, min{b,c})$, $(min{b,c},b)$ and $(min{b,c},c)$ all exist, with the following diagram commutes (denote $n:=min{b,c}$):

  #diagram($
             && c edge("dll", (c,a), ->) edge("drr",(c,b),->) edge("d",(c,n),->) \
            a && n edge("ll", (n,b), ->) edge("rr",(n,c),->) && b
           $)

  And, based on the fact that each pair of objects in $(ZZ,<=)$ as at most one morphism, $(c,n)$ must be the unique morphism. So, this category has product, with $b times c := min{b,c}$.
]

#example[Coproducts][
  Normally, "co-" naively indicates "reversing all arrows" in the category. So, coproducts can be thoought of as the "reverse" of everything, which can look into the category $C^(A,B)$ (instead of having a common source that point to each $A$ and $B$, we have $A$ and $B$ point to a common target). 
  
  So, we want the object to be the pair $(phi_1,phi_2)$ where $phi_1:A arrow.r Z$ and $phi_2:B arrow.r Z$, while the morphisms from pair $(phi_1,phi_2)$ (with target $Z_1$) to pair $(phi.alt_1, phi.alt_2)$ (with target $Z_2$), be morphisms $h:Z_1 arrow.r Z_2$, such that the following diagram commutes:

  #diagram($
             & Z_2 \ 
             A edge("ur", phi.alt_1, ->) edge("r",phi_1,->) & Z_1 edge("u", h, ->) & B edge("ul", phi.alt_2, ->) edge("l", phi_2,->)
           $)

  And, we want to define coproduct of $A$ and $B$ as the object $Z^*$ with two morphisms $(phi_1,phi_2)$ (placed in the position of $Z_1$) such that for every other $Z$ and $(phi.alt_1,phi.alt_2)$ (placed in the position of $Z_2$) has a unique morphism $h$. Which, we denote as $A product.co B$.
]
For similarity, here is an example in sets:
#example[Coproducts in Sets - Disjoint Union][
  In general, disjoint union of set $A,B$, is union $A' union.sq B'$, where $A' tilde.equiv A$ and $B' tilde.equiv B$, while $A' sect B'=emptyset$. For instance, take $A'={0} times A$ and $B'={1} times B$.

  Then, a natural "inclusion" $i_1:A arrow.r A product.co B$ and $i_2:B arrow.r A product.co B$ can be made, by $i_1(a) = (0,a)$ and $i_2(b) = (0,b)$ (since in this example we set $A product.co B := A' union.sq B'$ with them given as above).

  To claim that this is an initial object in the associated category, for any other set $Z$ with $phi_1:A arrow.r Z$ and $phi_2:B arrow.r Z$, we can define the map $sigma: A product.co B arrow.r Z$ as $sigma(0,a)=phi_1(a)$, while $sigma(1,b)=phi_2(b)$. Then, claerly the following is diagram commutes:

  #diagram($
             & Z \ 
             A edge("ur", phi_1,->) edge("r",i_1,->) & A product.co B edge("u",sigma,->) & B edge("ul",phi_2,->) edge("l",i_2,->)
           $)

  And, uniqueness of the map $sigma$ is enforced by how disjoint union is defined. Hence, $A product.co B$ with functions $(i_1,i_2)$ is clearly an initial object in the given category of $C^(A,B)$ (where $C$ is the category of sets).
]

The above is also a good example about terminal / final objects being not unique in general (but unique up to isomorphism). Which, it again reinforces the idea that products / coproducts in general is not unique, but they're all isomorphic.

\ 

However, given a category and subcategory of it, the product and coproduct could be drastically different: Given the category of groups and abelian groups, in both categories, the products are the same, namely the direct product of the groups; but, the two have different coproducts in general.

#proposition[In the category of abelian groups, products and coproducts are equivalent.][
  Given any abelian group $G,H$, their direct product $G times H$ is in fact the coproduct also: Given any other abelian group $K$ with two homomorphisms $phi_1:G arrow.r K$ and $phi_2:H arrow.r K$, the map $sigma:G times H arrow.r K$ by $sigma(g,h) = phi_1(g)phi_2(h)$ is a well-defined group homomorphism since: 
  $ sigma((g_1,h_1)(g_2,h_2)) = sigma(g_1g_2,h_1h_2) = phi_1(g_1g_2)phi_2(h_1h_2)=phi_1(g_1)phi_1(g_2)phi_2(g_1)phi_2(g_2) $
  $ = (phi_1(g_1)phi_2(h_1))(phi_1(g_2)phi_2(h_2)) = sigma(g_1,h_1)sigma(g_2,h_2) $ 
  (Note: This relation relies on the fact that $K$ is abelian).

  So, the following diagram commutes:
  
  #diagram($
             & K \
             G edge("ur",phi_1,->) edge("r",->) & G times edge("u",sigma,->) H & H edge("ul",phi_2,->) edge("l",->)
           $)

  Where the bottom two arrows are the natural "inclusion" $g arrow.r.bar (g,e_H)$ and $(e_G,h) arrow.l.bar h$.

  Also, the map $sigma$ is uniquely determined about where $phi_1,phi_2$ map the elements of $G$ and $H$ respectively (since all the $(g,e_H)$ and $(e_G,h)$ must be fixed by $phi_1$ and $phi_2$ respectively).

  Hence, $G times H$ is a coproduct also in the category of abelian groups, which normally denote as "direct sum" $G plus.circle H$.
]
#example[Product not as Coproduct in Groups][
  Choose $ZZ_2$ and $ZZ_3$ for example, and map them to $S_3$ the permutation group. Then, a map $phi_1:ZZ_2 arrow.r S_3$ must have $1_2 arrow.r.bar (1 2),(13), (23)$, or $e$, while a map $phi_2:ZZ_3 arrow.r S_3$ must have $1_3 arrow.r.bar (123),(132)$, or $e$.

  Suppose the contrary that $ZZ_2 times ZZ_3$ is the coproduct of the two desired groups, then there must exist unique map $sigma:ZZ_2 times ZZ_3 arrow.r S_3$ with the following diagram commutes:
  
  #diagram($
             & S_3 \
             ZZ_2 edge("r",->) edge("ur",phi_1,->) & ZZ_2 times ZZ_3 edge("u",exists ! sigma, ->) & ZZ_3 edge("l",->) edge("ul",phi_2,->)
           $)
  
  Which, the image of $sigma$ must be abelian. But, if given $phi_1(1_2)=(12)$ and $phi_2(1_3)=(123)$, with the above diagram commutes, $(12)$ and $(123)$ must be in the image of $sigma$, hence the image of sigma is not abelian (due to the fact that $(12)(123)=(23) != (13) =(123)(12)$), which forms a contradiction. So, $ZZ_2 times ZZ_3$ can't be a coproduct of $ZZ_2$ and $ZZ_3$.
]
So in general, we need some other tools to construct coproducts for groups in general (which is highly related to free groups).

#pagebreak()

= Free groups
The initial motivation, is that for any set $A$, we want to constructa group out of it "without" any special relations (hence, every special relations between any elements of some group constructed out of $A$ can be deduced by adding specific structure to the "relationless" group of $A$). Another thing is that we want such group to be the most efficient (and general).

\ 

For instance, given $A=emptyset$, then a trivial group ${e}$ technically has "no" relation for any element given in $emptyset$ (since there's no elements).

Then, given $A = {a}$, trivial group no longer works, since it requires $e:= a$, which $a$ must satisfy the relation $a^n = a$ for all $n in ZZ$, which is technically nontrivial as a relation. Instead, the infinite cyclic group $angle.l a angle.r = {a^n | n in ZZ}$ as the "free group" of $A$, since the element $a in A$ technically has no relation, besides the inevitable $a^0 = e$.

\ 

Overall, we want the construction of free group $F(A)$ of a set $A$ to be more general (or, as a universal property we can find for every set). Which (in the perspective I got from all the knowledge I have), free group $F(A)$ should satisfy: Given any group $G$ such that as a set $A subset.eq G$, there exists a unique map $phi_A:F(A) arrow.r G$, such that $phi_A(a)=a$ for all $a in A$. (Unfortunately this is not broad enough in general. We need $G$ to be arbitrary group, with set function $j:A arrow.r G$).

More formally, we'll define free groups as follow:

#definition[Free Group (idealized)][
  Given a set $A$, its free group $F(A)$ is a group where $A subset.eq F(A)$ (i.e. has natural inclusion $i:A arrow.r F(A)$), such that the pair $(F(A),i)$ is an initial object of the following category:

  Define category $cal(F)(A)$ to be with objects $(G,j)$, where $j:A arrow.r G$ is just a set function, and morphism $phi in Hom_(cal(F)(A))((G_1,j_1), G_2,j_2)$ is a group homomorphism $phi:G_1 arrow.r G_2$ such that the following diagram commutes:

  #diagram($
            G_1 edge("rr",phi,->) & & G_2 \
            & A edge("ul",j_1,->) edge("ur",j_2,->) 
           $)
]
One of the reasons they're expanded to arbitrary groups $G$ and set functions $j:A arrow.r G$ is because we want to eliminate all possible relations endowed in $A$, which having arbitray set function would include all possible relations one can define on $A$. And, having it as an "initial object" provides the fact that other ways of creating group relations on elements of $A$, can now be factored uniquely through a group homomorphism starting from $F(A)$ (i.e. can be constructed through adding extra group relations on $F(A)$).

If $F(A)$ exists, then in the previous section about initial objects, every free group of $A$ is isomorphic to each other as groups. So, it remains only to construct such group.
#thm("Construction of Free Groups")[For every set $A$, a free group exists.][

  #text(weight: "bold")[Construction of a Group:]

  Define $W(A):={e} union {a_1^(k_1)...a_n^(k_n) | n in NN, a_i in A, k_i = plus.minus 1}$, or the collection of all possible finite tuples of elements from $A$ (up to an "inverse" sign), where two tuples with different elements (or same elements with different order) are not the same. And, some naive relations we want includes:
  1. Given any $a_1^(k_1)...a_n^(k_n)$ and $b_1^(l_1)...b_m^(l_m)$ in $F(A)$, define $(a_1^(k_1)...a_n^(k_n)) dot (b_1^(l_1)...b_m^(l_m)):= a_1^(k_1)...a_n^(k_n)b_1^(l_1)...b_m^(l_m)$ (i.e. the group operation is "concatination" of finite tuples, which is clearly associatve).
  2. Given any $b in F(A)$, $e dot b = b dot e = b$ (i.e. operation with $e$ is essentially "concatinate nothing" to the tuples, or $e$ itself represens a tuple with zero word, or "nothing").
  3. For every $a in A$, the inverse is $a^(-1)$, satisfying $a a^(-1)=a^(-1)a=e$ (i.e. one can "subtract" words based on some properties, and the element $a^(-1)$ has inverse $a$).

  \ 
  
  But, this isn't the full version, since we want to define a well-defined relation to prevent redundancy. Which, we want this to be the most general, i.e. it operates on every part of the every possible words: For instance, given $x x x^(-1)y y^(-1) y$, we want it to be the same as $x y$ (i.e. cancel out every pair of $a a^(-1)$ possible).

  The way Aluffi constructs it is by setting an elementary reduction $r:W(A) arrow.r W(A)$, where for any tuples $w in F(A)$, we find the first occurance of some pair $a a^(-1)$ in $w$, and "delete" them. For instance, $r(x x^(-1)) = e$, and $r(x (y y^(-1)) x^(-1)) = x x^(-1)$. And, we say a tuple is #emph[reduced] if $r(w)=w$ (i.e. there's no redundancy, or cancellation possible).

  Which, since this reduction method deletes two element of the tuple each time, then for an $n$-tuple, there can have at most $floor(n/2)$ reductions. Hence, we can define the general reduction $R:W(A) arrow.r W(A)$ by $R(w) = r^(floor("length"(w)/2))(w)$ to be the "reduced form" or $w$ (where $e$ as the tuple of "nothing" is vacuously reduced).

  \ 

  Finally, we define the free group $F(A) := R(W(A))$, all the reduced words, then the full general rule becomes:
  - Given any $u,v in F(A)$, define $u dot v = R(u dot v)$ (where the second $u dot v$ is the operation "concatination" in $W(A)$).
  Under this definition, the operation is associative (since there's no ambiguity about the "reduced form" of a tuple), identity is $e$ in $W(A)$, and inverse $(a_1^(k_1)...a_n^(k_n))^(-1) = a_n^(-k_n)...a_1^(-k_1)$.

  \ 

  \ 

  #text(weight: "bold")[Verification of Universal Property:]

  Now, we claim that with the inclusion $i:A arrow.r F(A)$, the pair $(i, F(A))$ satisfies the desired universal property:

  Given any group $G$ with set function $j:A arrow.r G$, for the diagram to commute as we want, one must define the group homomorphism $phi:F(A) arrow.r G$ by $phi(e)=e_G$, $phi(a)=j(a)$ and $phi(a^(-1))=j(a)^(-1)$ for all $a in A$, and $phi(a_1^(k_1)...a_n^(k_n)) = j(a_1)^(k_1)...j(a_n)^(k_n)$ to form a group homomorphism. Which, this map is the only possible one for it to commute (since the generators of $F(A)$, namely all the $a$ and $a^(-1)$ with $a in A$, are already fixed by $j$). And, it's evident that the following diagram commutes:
  #diagram($
             F(A) edge("r",phi,->) & G \
             A edge("u",i,->) edge("ur",j,->)
           $)

  So, $(i, F(A))$ is in fact the initial object of the desired category.
]

\ 

The above constructs the "free-est" group when given a set $A$ (inside the category of Groups), but from the last section we know subcategory would have a different result in general for the category of abelian group. Again, we'll choose a similar category collecting all objects of $(G,j)$, but here $G$ is required to be abelian, while $j:A arrow.r G$ remains as arbitrary set function, and define $F^"ab" (A)$ as an abelian group such that with some set function $i:A arrow.r F^"ab" (A)$, the pair $(F^"ab" (A), i)$ is the initial object of the category. 

Again, based on the definition of initial object, such free abelian group is unique up to isomorphism, so it suffices to show the existence.

#thm("Construction of free Abelian Groups")[
  Free Abelian Group exists for all set $A$.
][
  First, given $A={1,...,n}$, consider $ZZ^(plus.circle n):= ZZ plus.circle...plus.circle ZZ$ with total of $n$ times, which acts the same as $ZZ^n$ like direct product (under finite sense), and as a coproduct of the category of abelian group. 

  To claim that it is the free abelian group, we'll take the function $f:A arrow.r ZZ^(plus.circle n)$ by $f(i) = e_i = (0,...,1,...,0)$ (having $1$ at the $i^"th"$ entry). Which, given any other pair $(G, j)$ for abelian group $G$ and function $j:A arrow.r G$ (which, we denote the operation of $G$ as addition, so can treat addition $n$ times as "multiplying by $n$").

  Then, in case for the diagram we desired to commute, we need $phi:ZZ^(plus.circle n) arrow.r G$ to satisfy $phi(e_i) = j(i)$ for all given $i$, and to make $phi$ into a group homomorphism, any element $b = sum_(i=1)^n k_i e_i$ for some $k_i in ZZ$, must have the image $phi(b)= sum_(i=1)^n k_i phi(e_i) = sum_(i=1)^n k_i j(i)$. Which, $phi$ is uniquely determined. To make sure it is a group homomorphism, since for any $b,c in ZZ^(plus.circle n)$, we have $b=sum_(i=1)^n k_i e_i$ and $c=sum_(i=1)^n l_i e_i$, then:
  $ phi(b+c) =phi(sum_(i=1)^n (k_i+l_i)e_i) = sum_(i=1)^n (k_i+l_i)j(i) = sum_(i=1)^n k_i j(i) + sum_(i=1)^n l_i j(i) = phi(b)+phi(c) $
  Which, the second last equality is true based on the abelian condition. So, any pair $(G, j)$ would have the following diagram commutes:
  
  #diagram($
             ZZ^(plus.circle n) edge("r",phi,->) & G\ 
             A edge("u", f, ->) edge("ur", j, ->)
           $)

  \ 

  Now in general, we can mimic a similar claim about finding a "direct sum" of $ZZ$ with respect to all the elements in $A$, which because of the finite sum condition, we want it to be a sequence of elements (which has a 1-to-1 correspondance to $A$, like a basis) such that only finitely many are nonzero (so it is a finite sum of the "basis" elements).

  We can define $ZZ^(plus.circle A)$ as the collection of sequences $(k_alpha)_(alpha in A)$ such that each $k_alpha in ZZ$, and only finitely many can be nonzero, with each summation being performed "entry wise" (or summing up the ones with the same index). 
  
  Another definition can be made through the Homset: Since $ZZ$ is an additive group, then it automatically make the collection of set functions $Hom_"set" (A, ZZ)$ into a group (like how we add / subtrace real-valued functions). Which, define $ZZ^(plus.circle n)$ as a subset of $Hom_"set" (A,ZZ)$, such that every function $h:A arrow.r ZZ$ has image with finite elements (i.e. finitely many inputs can output nonzero numbers). 
  
  Which, the collection ${h_alpha: A arrow.r ZZ | alpha in A}$ by $h_alpha(alpha)=1$ while $h_alpha(x)=0$ for all $x != alpha$, in fact forms a generating set of $ZZ^(plus.circle A)$, which a natural function $i:A arrow.r A^(plus.circle A)$ by $j(alpha) = h_alpha$ is a natural set function of $A$ into $ZZ^(plus.circle A)$; on the other hand, every function can be expressed as finite integer combinations of functions in the generating set (since if $h$ satisfies $h(alpha) = k_alpha$ for precisely $alpha_1,...,alpha_n$ while the rest are zero, then $h = sum_(i=1)^n k_(alpha_i) h_(alpha_i)$ as functions).

  Finally, for any pair $(G, j)$ with $G$ being abelian and $j:A arrow.r G$, for the desired diagram to commute, define $phi:ZZ^(plus.circle A) arrow.r G$ by $phi(h_alpha) = j(alpha)$, and to make it a group homomorphism, for any finite list $alpha_1,...,alpha_n in A$, we must have $phi(sum_(i=1)^n k_(alpha_i)h_(alpha_i)) =sum_(i=1)^n k_(alpha_i) j(alpha_i)$. Such constraint (of diagram commuting) enforces $phi$ to be unique, and the final definition enforces it to be a group homomorphism.

  Since the following diagram commutes for all pairs of $(G,j)$, we can claim that $ZZ^(plus.circle A)$ is a free abelian group of $A$:

  #diagram($
             ZZ^(plus.circle A) edge("r",phi,->) & G\ 
             A edge("u",i,->) edge("ur",j,->)
           $)
]

Which, free group is closely related to coproducts in the category of groups and abelian groups. Beforehand we know for abelian groups, product and coproduct turns out to be isomorphic, so we know $F^"ab" ({x_1,...,x_n}) tilde.equiv ZZ^(plus.circle n) tilde.equiv ZZ^n$, which is the $n^"th"$ coproduct of $ZZ$. Which, free group in category of group is similar:
#problem[(Aluffi II 5.6, 5.7) Prove that the group $F({x,y})$ is a coproduct $ZZ * ZZ$ of $ZZ$ in the category of groups. Which, inductively $F({x_1,...,x_n})$ is an $n^"th"$ coproduct of $ZZ$.][
  For any group $G$, with group homomorphisms $f_1,f_2:ZZ arrow.r G$, we know the pair of functions $i_x,i_y: ZZ arrow.r F({x,y})$ by $i_x (n)=x^n$ and $i_y (n)=y^n$ are well-defined group homomorphisms. Which, to make the diagram for coproduct to commute, a map $phi:F({x,y}) arrow.r G$ by $phi(x) = f_1(1)$ and $phi(y) = f_2(1)$ are required, where $phi(a_1^(k_1)...a_n^(k_n)) = i_(a_1) (1)^(k_1)... i_(a_n) (1)^(k_n)$ is required to be a group homomorphism.

  Which, based on the construction the following diagram commutes:

  #diagram($
             & G \
             ZZ edge("ur",f_1,->) edge("r",i_x,->) & F({x,y}) edge("u",phi, ->) & ZZ edge("ul",f_2,->) edge("l", i_y, ->)
           $)

  $phi$ is uniquely determined by $G,f_1,f_2$ since with $x,y$ (generators of $F({x,y})$) being mapped to by the generators of $ZZ$, then with $f_1,f_2$ fixes where the generators go, it is uniquely determined. Hence, $F({x,y})$ satisfy the universal property of being a coproduct of $ZZ$.

  Which, inductively (since finite coproduct just like product is unique up to isomorphism), then $F({x_1,...,x_n})$ is an $n^"th"$ coproduct of $ZZ$.
]
#problem[(Aluffi II 5.8) More generally, $F(A product.co B) = F(A) * F(B)$ and that $F^"ab" (A product.co B) = F^"ab" (A) plus.circle F^"ab" (B)$ (i.e. $F, F^"ab"$ "preserves coproducts" when going from category of sets to groups / abelian groups).][
  WLOG, can assume $A,B$ are disjoint as sets (since $A product.co B$ is generated through union of disjoint isomorphic copies of $A$ and $B$). Then, given $F(A), F(B)$, since $A product.co B$ can be viewed as a set of disjoint union of $A$ and $B$ (which means the generators of free groups are contained in each other), then we naturally get $F(A), F(B) subset.eq F(A product.co B)$, so there are natural inclusion maps (as group homomorphisms).

  
]
