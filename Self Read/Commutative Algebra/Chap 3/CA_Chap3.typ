#import "@preview/rubber-article:0.4.1": *
#import "@preview/ctheorems:1.1.3": *

//basic template setup
#show: article.with(
  header-display: true,
  eq-numbering: "(1.1)",
  eq-chapterwise: true,
  margins: 1.0in,
)
#show: thmrules

//math environment setup
#let myQuestion = thmbox(
  "theorem", "Question",
  fill: rgb(232,232,248),
  stroke: rgb(46,46,50)
)
#let myThm = thmbox(
  "theorem", "Theorem",
  fill: rgb(22, 106, 250, 40),
  stroke: rgb(5, 27, 62)
)
#let myDef = thmbox(
  "theorem", "Definition",
  fill: rgb(0,200,220, 20),
  stroke: rgb(0,43,43)
)
#let myProp = thmbox(
  "theorm", "Proposition",
  fill: rgb(50,250,50, 20),
  stroke: rgb(10,50,10) 
)
#let myLemma = thmbox(
  "theorem", "Lemma",
  fill: rgb(96,250, 153, 30),
  stroke: rgb(20,50,35)
)

//common syntaxes needed
#let neq = $!=$
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
//complex 
#let Real = $"Re"$
#let Imag = $"Im"$ //also used for image
#let Arg = $"Arg"$
#let Res = $"Res"$
//lie algebra
#let gl = $frak("gl")$
#let sl = $frak("sl")$
#let sp = $frak("sp")$


//start document
#maketitle(
  title: "Commutative Algebra Chapter 3",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

= D//1
#myQuestion[
  Let $S$ be a multiplicatively closed subset of a ring $A$, and let $M$ be a finitely generated $A$-module. Prove that $S^{-1}M=0$ if and only if there exists $s in S$ such that $s M=0$.
]
#text(weight: "bold")[Pf:]

$==>:$ Suppose $S^(-1)M=0$. For the case where $M=A x$ for some $x in M$, since $x/1 = 0 in S^{-1}M$, there exists $u in S$, such that $u x = 0$. Hence, for all $y in M$, because $y=r x$ for some $r in A$, then $u y = u(r x) = r(u x)=r dot 0 = 0$, showing that $u M = 0$.

Now in general, suppose $M = A x_1+...+ A x_n$ for some $x_1,...,x_n in M$, by the logic of submodule generated with $1$ element above, there exists $s_1,...,s_n in S$, where $s_i(A x_i)=0$. Hence, take $s = s_1...s_n in S$, we have $s M = 0$ (since all generators were annihilated).

\ 

$<==:$ Suppose there exists $s in S$ where $s M=0$, then obviously $S^(-1)M=0$, since for all $x in M$, $s (1 dot x - 1 dot 0)=0 ==> x/1 = 0/1 = 0 in S^(-1)M$, hence $S^(-1)M=0$.

= D //2
#myQuestion[
  Let $a$ be an ideal of a ring $A$, and let $S=1+a$. Show that $S^(-1)a$ is contained in the Jacobson radical of $S^(-1)A$.
]
#text(weight: "bold")[Pf:]

First, it is clear that $S$ is multiplicatively closed, since $1=1+0 in 1+a$, and given $x,y in a$, we have $(1+x)(1+y)=1+(x+y+x y) in 1+a = S$.

Now, given any $1+x in S$ and $y in a$, we have $y/(1+x) in S^(-1)a$. Then, given any $z/(1+w) in S^(-1)A$ (where $w in a$ and $z in A$), consider $1-z/(1+w) dot y/(1+x)$:
$ 1-(z y)/(1+(w+x+w x)) = (1+(w+x+w x - z y))/(1+(w+x+w x)) $
Where, since $x,y,w in a$, we have $w+x+w x in a$, and $w+x+w x-z y in a$, showing that both elements in the numerator and the denominator belong to $S=1+a$, hence the above element is invertible.

With the choice of $z/(1+w) in S^(-1)A$ and $y/(1+x) in S^(-1)a$ being arbitrary, we get $S^(-1)a$ is fully contained in the Jacobson radical of $S^(-1)A$.


= D // 3
#myQuestion[
  Let $A$ be a ring, let $S$ and $T$ be two multiplicatively closed subsets of $A$, and let $U$ be the image of $T$ in $S^(-1)A$. Show that the rings $(S T)^(-1)A$ and $U^(-1)(S^(-1)A)$ are isomorphic.
]
#text(weight: "bold")[Pf:]

First, it's clear that $S T$ is multiplicatively closed, given $S$ and $T$ both are (since $1=1 dot 1 in S T$, and $(s t)(s' t') = (s s')(t t') in S T$, given $s t, s' t' in S T$).

Consider the map $(S T)^(-1)A arrow.r U^(-1)(S^(-1)A)$ by $x/(s t) arrow.r.bar (x\/s)/(t\/1)$: To prove that it's well-defined, suppose $x/(s t)=x'/(s't')$ in $(S T)^(-1) A$, there exists $u v in S T$, where $(x(s't')-x'(s t))(u v) = 0$. Hence in $S^(-1)A$, we get (note that $u in S$ and $v in T$):
$ ((x u s')/1 dot t'/1 - (x' u s)/1 dot t/1)dot (v/1)=0 $
Which, with $U$ being multiplicatively closed (the image of $T$ in $S^(-1)A$), this implies the following in $U^(-1)(S^(-1)A)$:
$ (x u s' \/ 1)/(t\/1) = (x' u s\/1)/(t'\/1) ==> (x\/s)/(t\/1)=(x'\/s')/(t'\/1) $
Where, the step above is multiplying $(1\/u s s')/1$ in $U^(-1)(S^(-1)A)$.

\ 

The defiend map is a ring homomorphism: Given $x_1/(s_1t_1),x_2/(s_2t_2) in (S T)^(-1)A$, the following equality is true for addition:
$ x_1/(s_1t_1)+x_2/(s_2t_2)=(x_1(s_2 t_2)+x_2(s_1 t_1))/(s_1s_2t_1t_2) arrow.r.bar 1/(t_1t_2\/1)((x_1(s_2t_2)+x_2(s_1t_1))/(s_1s_2)) $
$ = 1/(t_1\/1) dot 1/(t_2\/1)(x_1/s_1 dot t_2/1 + x_2/s_2 dot t_1/1) = (x_1\/s_1)/(t_1\/1)+(x_2\/s_2)/(t_2\/1) $
Where, the last part is precisely the image of $x_1/(s_1t_1)$ plus the image of $x_2/(s_2t_2)$, showing the additive property.

For multiplication, we have the following:
$ x_1/(s_1t_1)dot x_2/(s_2t_2)=(x_1x_2)/(s_1s_2t_1t_2) arrow.r.bar 1/(t_1t_2\/1)((x_1x_2)/(s_1s_2)) = (x_1\/s_1)/(t_1\/1)dot (x_2\/s_2)/(t_2\/1) $
The second part is precisely the image of the two components multiplied together, proving the multiplicative property. Hence, it's indeed a ring homomorphism.

\ 

Finally, to show it's an isomorphism, it's clear that the map is surjective (since any $(x\/s)/(t\/1) in U^(-1)(S^(-1)A)$ is mapped to by $x/(s t)$). To show injectivity, suppose $x/(s t) arrow.r.bar (x\/s)/(t\/1) = 0 in U^(-1)(S^(-1)A)$, we have $t'/1 dot x/s = 0$ for some $t'/1 in U$, hence with $(x t')/s = 0 in S^(-1)A$, there exists $u in S$, where $u(x t') = 0$, so $u t' in S T$ satisfies $x(u t')=0$, proving $x/(s t)= 0$ in $(S T)^(-1)A$. Hence, the map is also injective, proving it's an isomorphism.

= ND //4
#myQuestion[
  Let $f:A arrow.r B$ be a homomorphism of rings and let $S$ be a multiplicatively closed subset of $A$. Let $T=f(S)$ (also multiplicatively closed). Show that $S^(-1)B$ and $T^(-1)B$ are isomorphic as $S^(-1)A$-modules.
]
#text(weight: "bold")[Pf:]

= D //5
#myQuestion[
  Let $A$ be a ring. Suppose that for each prime ideal $P$, the local ring $A_P$ has no nilpotent element $!= 0$. Show that $A$ has no nilpotent element $!=0$. If each $A_P$ is an integral domain, is $A$ necessarily an integral domain?
]

#text(weight: "bold")[Pf:]

We'll prove the contrapositive. Suppose $x != 0$, then with $x$ being nilpotent, we have $"Ann"(x)!=0, A$ (the ideal of annihilator of $x$), hence it is contained in some maximal ideal $M$ (which is also prime). Then, consider the local ring $A_M$, since $"Ann"(x) subset.eq M$, so $"Ann"(x) sect (A\\M)=emptyset$. Hence, for all $s in (A\\M)$, we have $s x != 0$, showing that $x/1!=0 in A_M$. However, with $x$ being nilpotent, $x/1!=0$ is also nilpotent.

Take the contrapositive, we get if all local ring has no nonzero nilpotent element, it enforces $x=0$, so all nilpotent element is $0$.

\ 

As a counterexample, consider $ZZ_6$: As a ring, it is not an integral domain (since $2 dot 3=6 equiv 0 mod 6$). But, its only proper ideals are ${0,2,4} tilde.equiv ZZ_3$ and ${0,3} tilde.equiv ZZ_2$, where both are prime ideals (first quotient obtains $ZZ_2$, while the second quotient obtains $ZZ_3$).

For the first prime ideal, suppose $x/y dot z/w = 0$ in the associated local ring (where $y,w in {1,3,5}$, and $x,z in ZZ_6$), then there exists $a in {1,3,5}$, where $a(x z)equiv 0 mod 6$. Given that $1,5$ are invertible, if $a=1,5$ we must have $x z$ divisible by $6$, so at least one is divisible by $2$ (similarly, if $a=3$, $x z$ is divisible by $2$, implying one of them is divisible by $2$). Regardless of the case, WLOG given that $x$ is divisible by $2$, then with $3 dot x equiv 0 mod 6$ (and $3 in {1,3,5}$), then $x/y = 0$ in the corresponding local ring. This proves the first local ring is an integral domain.


Now, for the second prime ideal, suppose $x/y dot z/w=0$ in the associated local ring (where $y,w in {1,2,4,5}$ this time). Then, there exists $a in {1,2,4,5}$ where $a(x z)equiv 0 mod 6$. Notice that $a$ is not divisible by $3$, while $a(x z)$ is, hence $(x z)$ is divisible by 3, showing (WLOG) that $x$ is divisible by $3$. Hence, take $2$ in the corresponding multiplicatively closed set, $2 dot x equiv 0 mod 6$, showing $x/y=0$ in the local ring. Hence, the second local ring is again an integral domain.


= ND//6

#myQuestion[
  Let $A$ be a ring $!=0$ and let $Sigma$ be the set of all multiplicatively closed subsets $S$ of $A$ such that $0 in.not S$. Show that $Sigma$ has maximal elements, and that $S in Sigma$ is maximal if and only if $A\\S$ is a minimal prime ideal of $A$.
]
#text(weight: "bold")[Pf:]

It's our beloved Zorn's Lemma again :)

Given the definition of $Sigma$, and impose a partial order on it, sch that $S<= T$ iff $S subset.eq T$ (which is a partial order, since $S<=S$, $S<=T$ and $T<=S$ implies $S=T$, and $S<=T$ and $T<=U$ implies $S<=U$).

Now, given any chain $C subset.eq Sigma$, take the set $S_C = union_(T in C)T$. Since each $T in C$ contains $1$, then $S_C$ clearly contains $1$; and, given $x,y in S_C$, by definition there exists $T_1,T_2 in C$, such that $x in T_1$ and $y in T_2$. Whic, by the property of chains, since $T_1 <= T_2$ or $T_2<= T_1$ (WLOG, assume $T_1 <= T_2$, or $T_1 subset.eq T_2$), we get $x,y in T_2$. Hence, with $T_2$ being multiplicatively closed, $x y in T_2 subset.eq S_C$, concluding that $S_C$ is multiplicatively closed.

Also, since each $T in C$ doesn't contain $0$, then $S_C$ doesn't contain $0$. So, $S_C in Sigma$, while every $T in C$ satisfies $T subset.eq S_C$ (or $T<=S_C$ given the partial order), hence $S_C$ is an upper bound of $C$. Therefore by Zorn's Lemma, there exists a maximal element in $Sigma$.

\ 

For the second part:

$==>:$ Suppose $S$ is maximal, and take $P=A\\S$. Given any $r in P$, since $union.big_(n in NN)r^n S$ is a multiplicatively closed subset strictly containing $S$ (since $r$ is in the set, while not in $S$, and $r^n s_1 dot r^m s_2 = r^(n+m) dot (s_1 s_2) in r^(n+m)S$), then by maximality of $S$ we must have $0 in union.big_(n in NN)r^n S$. Hence, $0=r^n s$ for some $n in NN$ and $s in S$.

  So, given any $a,b in P$, since there exists $n,m in NN$ and $s_1,s_2 in S$, such that $0 = a^n s_1=b^m s_2$, take $(a-b)^(n+m)(s_1 s_2)$, this term provides $0$ (since within every term in the expanded summation, it is of the form $mat(n+m;k)a^k s_1 dot b^(n+m-k)s_2$, if $k<n$ then $b^m s_2 = 0$ is in the product, so it's $0$; else if $k >= n$ then $a^n s_1=0$ is also in there, so every term is $0$). Then, since $union.big_(k in NN)(a-b)^k S$ contains $0$, $a-b in.not S$ (or else this union is just $S$), hence $a-b in P = A\\S$. So, $P$ is indeed an additive subgroup.

  Similarly, given any $r in A$ and $a in P= A\\S$, since there exists $n in NN$ and $s in S$, satisfying $a^n s = 0$, then $union.big_(k in NN)(r a)^k S$ contains $0$ (take $s in S$ and $k = n$), showing $r a in.not S$, or $r a in P$, which shows $P=A\\S$ is an ideal.

  Then, to show it's a minimal prime ideal, recall that $P$ is prime $<==>$ $A\\P$ is multiplicative (that's not containing $0$), then with $S = A\\(A\\S) = A\\P$ being multiplicative, $P=A\\S$ is prime. Also, this enforces $P$ to not contain any proper prime ideal, since if $P' subset.neq P$ is prime, then $A\\P'$ is multiplicative (and not containing 0), with $S=A\\P subset.neq A\\P'$, which violates the maximality of $S$. Hence, $P=A\\S$ must be a minimal prime ideal.

$<==:$ Now,

= ND//7
#myQuestion[
  A multiplicatively closed subset $S$ of a ring $A$ is said to be #emph[Saturated] if
  $ x y in S <==> x, y in S $
  Prove that 
  1. $S$ is saturated $<==>$ $A\\S$ is a union of prime ideals
  2. If $S$ is any multiplicatively closed subset of $A$, there is a unique smallest saturated multiplicatively closed subset $overline(S)$ containing $S$, and that $overline(S)$ is the complement in $A$ of the union of the prime ideals which do not meet $S$. (Note: $overline(S)$ is called the #emph[saturation] of $S$).

  Given $S=1+a$ where $a$ is an ideal of $A$, find $overline(S)$.
]
#text(weight: "bold")[Pf:]
1. $==>:$ Suppose $S$ is saturated. Given $S^(-1)A$, since all of its prime ideals corresponds to all prime ideals in $A$ that don't intersect $S$, we claim that $A\\S = union_(i in I)P_i$, where $I$ collects all prime ideals $P_i subset.neq A$ that don't intersect $S$.

  By definition, it is clear that $union_(i in I)P_i subset.eq A\\S$, since each $P_i sect S=emptyset$, so $P_i subset.eq A\\S$, hence the union is also included in $A\\S$.

  Now, given any $x in A\\S$, we have $x/1 in S^(-1)A$ not being invertible: Suppose it is invertible, then there exists $s in S$, where $s(x-1)=0$, or $s x = s in S$, but this enforces $x in S$ due to saturation property, which is a contradiction. So, $(x/1) subset.neq S^(-1)A$ is a proper ideal, which is contained in some prime ideal $S^(-1)P$ of $S^(-1)A$ (coresponds to prime ideal $P$ in $A$). Then, since $x/1 in S^(-1)P$, $x/1 = p/s$ for some $p in P$ and $s in S$, or $u(s x-p) = 0$ for some $u in S$, hence $(u s)x = u p in P$.
  Finally, since $P$ doesnt intersect $S$ (by the 1-to-1 correspondance of prime ideals in $S^(-1)A$ and $A$), with $(u s)x in P$, while $u s in S$ (or $(u s) in.not P$), we must have $x in P$. Hence, $x in union_(i in I)P_i$ (since $P$ is one of the index prime ideals).

  As a conclusion, $union_(i in I)P_i = A\\S$.

  $<==:$ Given that $A\\S$ is a union of prime ideals, say $A\\S = union_(i in I)P_i$, $S$ is multiplicatively closed (so $x,y in S$ implies $x y in S$). Now, suppose $x y in S$, to prove that $x,y in S$, suppose the contrary that this is false. Then, either $x in.not S$ or $y in.not S$ (WLOG, assume it's $x$). Then, since $x in A\\S$, $x in P_i$ for some index $i$. Hence, $x y in P_i subset.eq A\\S$, which causes a contradiction. Hence, we must have $x, y in S$ (so $x y in S$ implies $x,y in S$). This proves that $S$ is saturated.

  \ 

2. Given $S$ any multiplicatively closed subset of $A$ (specifically required to not include $0$), take $I$ being an index set collecting precisely all prime ideals $P_i$ ($i in I$) that doesn't intersect $S$. Then, we have $union_(i in I)P_i subset.eq A\\S$. Then, set $overline(S) = A\\union_(i in I)P_i$, it is saturated, and we have $A\\overline(S) - union_(i in I)P_i subset.eq A\\S$, showing $S subset.eq overline(S)$. Hence, every multiplicatively closed subset has a saturated subset containing it.

  Now, to prove uniqueness as a smallest saturated subset containing $S$, suppose some $overline(S)'$ saturated, satisfies $S subset.eq overline(S)' subset.eq overline(S)$, as a result we have $union_(i in I)overline(S) subset.eq A\\overline(S)' subset.eq A\\S$, where by saturated property we have $A\\overline(S)' = union(j in J)P_j'$ (where each $P_j'$ is a prime ideal that doesn't intersect $S$). However, by definition $I$ collects all prime ideals $P_i$ that don't intersect $S$, then each $P_j' = P_i$ for some index $i in I$, showing $A\\overline(S)' = union_(j in J)P_j' subset.eq union_(i in I)P_i = A\\overline(S)$. Hence, $A\\overline(S)' = A\\overline(S)$, showing $overline(S)=overline(S)'$. So, $overline(S)$ is indeed unique, as of a smallest saturated subset containing $S$.

\ 

Finally, given a proper ideal $a subset.neq A$, it's clear that $S=1+a$ is multiplicatively closed, without containing $0$. Then, let index set $I$ collects precisely all prime ideals $P_i$ with $P_i sect S=emptyset$, then $overline(S) = A\\union.big_(i in I)P_i = sect.big_(i in I)(A\\P_i)$. 

Now, we claim that $P sect (1+a)=emptyset$ iff $a subset.eq P$:
- First, if $a subset.eq P$, then $(1+a)sect P=emptyset$, since if there exists $k in a$ satisfying $1+k in P$, then since $k in a subset.eq P$, we have $1 = (1+k)-k in P$, showing that $P=A$. Yet, this contradicts the assumption of $P$ being prime, so we must have no $k in a$ satisfying $1+k in P$, showing that $(1+a)sect P=emptyset$.
- Then, suppose $(1+a)sect P=emptyset$, but $a subset.eq.not P$

\ 

#text(weight:"bold")[Rmk:] Since $emptyset$ is not counting as a union of prime ideals, so $S=A$ is a special case for saturated subsets. Given $0 in S$ and $S$ is saturated provides that $x dot 0=0 in S$ for all $x in A$, hence $x in S$, showing $S=A$. So, the only saturated subset containing $0$ is $A$ itself.

= ND//8
#myQuestion[
  Let $S,T$ be multiplicatively closed subsets of $A$, such that $S subset.eq T$. Let $phi:S^(-1)A arrow.r T^(-1)A$ be the homomorphism which maps each $a/s in S^(-1)A$ to $a/s in T^(-1)A$. Show that the following statements are equivalent:
  
  1. $phi$ is bijective.
  2. For each $t in T$, $t/1$ is a unit in $S^(-1)A$.
  3. For each $t in T$, there exists $x in A$ such that $x t in S$.
  4. $T$ is contained in the saturation of $S$.
  5. Every prime ideal which meets $T$ also meets $S$.
]
#text(weight: "bold")[Pf:]

$1==> 2:$ Suppose $phi$ is bijective, then for each $t in T$, given $t/1 in S^(-1)A$, it maps to itself, or $phi(t/1) = t/1$ (former in $S^(-1)A$, latter in $T^(-1)A$). Which, given that $phi$ is bijective, there exists a unique $a/s in S^(-1)A$, such that $phi(a/s)=1/t in T^(-1)A$. Hence, we get $phi(t/1) dot phi(a/s) = phi(t/1 dot a/s) = t/1 dot 1/t = 1$, hence with $phi(1)=1$, we must have $t/1 dot a/s = 1$, showing $t/1$ is a unit in $S^(-1)A$.

\ 

$2==>3:$ Suppose for each $t in T$, $t/1$ is a unit in $S^(-1)A$, then there exists $a/s in S^(-1)A$, such that $t/1 dot a/s = 1/1$. Hence, there exists $u in S$, such that $u(t a- s)=0$, or $(u a)t = u s in S$ (recall that $s in S$ by definition). Hence, take $x=u a in A$, we have $x t in S$.

\ 

$3==>4:$ Supppose for each $t in T$, there exists $x in A$ such that $x t in S$, then given $overline(S)$ as the saturation of $S$, with $x t in S subset.eq overline(S)$, then $x t in overline(S)$, showing that $T subset.eq overline(S)$ (so $T$ contains in the saturation of $S$).

\ 

$4==>5:$ Given that $T$ is contained in the saturation of $S$ (denoted $overline(S)$), then suppose a prime ideal $P$ meets $T$, we have $P sect overline(S)!= emptyset$. Recall from the previous exercise that $A\\overline(S) = union.big_(i in I)P_i$, is the union of all prime ideals $P_i$not intersecting $S$. Then, since $P sect overline(S) != emptyset$, $P subset.eq.not A\\overline(S)$, so $P$ is not part of the union. Hence, $P sect S != emptyset$.

\ 

$5==>1:$ Suppose every prime ideal meeting $T$ also meets $S$, then given any prime ideal $P$ with $P sect S=emptyset$ (which $P subset.eq A\\overline(S)$), we must have $P sect T=emptyset$, showing $P subset.eq A\\overline(T)$, hence $overline(T) subset.eq overline(S)$.

  First, if $a/s in S^(-1)A$ satisfies $phi(a/s)=a/s=0 in T^(-1)A$, then there exists $t in T$, such that $t a = 0$. There are two cases:
  - Suppose $t$ is a unit, then we must have $a=0$ regardless, so $a/s=0$.
  - Suppose $t$ is not a unit, there exists prime ideal $P$ containing $t$, hence this prime ideal intersects $T$, which also intersects $S$. So, there exists $u in S sect P$, such that $u(t a)=0$.

  Given any $a/t in T^(-1)A$

= ND//9
#myQuestion[
  The set $S_0$ of all non-zero-divisors in $A$, is a saturated multiplicatively closed subset of $A$ (not containig $0$). Hence, the set $D$ of zero-divisors in $A$ is a union of prime ideals. Show that every minimal prime ideal of $A$ is contained in $D$ (using Exercise $6$).

  The ring $S_0^(-1)A$ is called the #emph[Total Ring of Fractions] of $A$. Prove:
  1. $S_0$ is the largest multiplicatively closed subset of $A$, which the homomorphism $A arrow.r S_0^(-1)A$ is injective.
  2. Every element in $S_0^(-1)A$ is either a zero-divisor or a unit.
  3. Every ring in which every non-unit is a zero-divisor is equal to its total ring of fractions (i.e. $A arrow.r S_0^(-1)A$ is bijective).
]
#text(weight: "bold")[Pf:]

By Exercise $6$, $P$ is a minimal prime ideal $<==>$ $A\\P$ is a maximal multiplicatively closed subset (and, this maximal multiplicatively closed subset is saturated since its complement is $P$, a prime ideal by Exercise 7). Then, suppose 
