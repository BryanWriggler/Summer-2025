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
//analysis 
#let Vol = $"Vol"$
//algebra
#let Hom = $"Hom"$
#let End = $"End"$
#let Aut = $"Aut"$
#let Coker = $"Coker"$
#let Gal = $"Gal"$
#let Nil = $"Nil"$
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
  title: "Commutative Algebra Chapter 1 Problems",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

= D//1.13
#myQuestion[
  Exercise 1.13 (unsolved);

  + $sqrt(I)=R <==> I=R$.
  + If ideal $P$ is prime, then $sqrt(P^n)=P$ for all $n in NN$.
]<q1.13>
#text(weight: "bold")[Pf:]

+ $==>:$ If $sqrt(I) = R$, then since $R=sqrt(I) = phi^(-1)("Nil"(R\/I))$ (where $phi$ is the projection onto $R\/I$), then we have $"Nil"(R\/I) = R\/I$. However, if ring $S != (0)$, then $"Nil"(S) subset.neq S$, so since $"Nil"(R\/I) = R\/I$, we must have $R\/I = (0)$, showing that $I=R$.
  $<==:$ If $I=R$, it follows that $sqrt(I)=R$.

  \ 

+ Given $P$ is a prime ideal, then for any $n in NN$, any $x in sqrt(P^n)$ satisfies $x^k in P^n subset.eq P$, hence by induction one can prove that $x in P$. So, $sqrt(P^n)subset.eq P$. Also, for all $x in P$, $x^n in P^n$, hence $P subset.eq sqrt(P^n)$, eventually proving that $sqrt(P^n)=P$.

= D//1
#myQuestion[
  Let $x$ be a nilpotent element of a ring $R$. Show that $1+x$ is a unit is $R$. Deduce that the sum of a nilpotent element and a unit is a unit.
]<q1>
#text(weight: "bold")[Pf:]

Given that $x in R$ is nilpotent, then $x^k=0$ for some $k in NN$ (also, this implies that $y=-x$ is also nilpotent with the same constant).

Then, $1+x = 1-(-x)=1-y$, which consider the following equation:
$ 1 = 1-0 = 1-y^k = (1-y)(sum_(i=0)^(k-1)y^i) $
In other words, the above term is the inverse of $1-y = 1+x$, which implies it is invertible.

Now, for any unit $u in R$ and nilpotent $x in R$, since $u+x = u(1+u^(-1)x)$, where $u^(-1)x$ is nilpotent, then $u+x$ is product of two units, hence is a unit.

= ND//2
#myQuestion[
  Let $R$ be a ring. Let $f=a_0+a_1x+...+a_n x^n in R[x]$. Prove that:
  + $f$ is a unit $<==>$ $a_0$ is a unit in $R$ and $a_1,...,a_n$ are nilpotent.
  + $f$ is nilpotent $<==>$ $a_0,...,a_n$ are nilpotent.
  + $f$ is a zero-divisor $<==>$ there exists $a != 0$ in $R$ such that $a f=0$.
  + $f$ is primitive if $(a_0,...,a_n)=R$ (as an ideal). Prove that $f,g in R[x]$, then $f g$ is primitive $<==>$ $f$ and $g$ are primitive.
]<q2>
#text(weight: "bold")[Pf:]
+ $==>$: Given $f=a_0+a_1x+...+a_n x^n$ is a unit, there exists $g=b_0+b_1x+...+b_m x^m$, where $f g = 1$. Which, the constant coefficient is given by $a_0 b_0 = 1$, so $a_0, b_0$ are both units.

  Now, we'll use induction to prove that $a_n^(r+1)b_(m-r)$ is nilpotent, given $0 <= r <= m$: First consider the base case $r=0$, the coefficient for degree $(n+m-r) = n+m$ is given by $a_n b_m = 0$. Then, for $r=1$, the coefficient for $n+m-r$ is given by $a_(n-1)b_m + a_n b_(m-1)= 0$, multiply by $a_n$ on both sides, we get:
  $ a_(n-1)b_m a_n + a_n^2 b_(m-1) = 0 ==> a_n^2 b_(m-1) =0 $
  Now, suppose for given $0 <= r < m$, the equation is true, then for $r+1$, we get the coefficient of degree $(n+m-(r+1))$ be as follow:
  $ sum_(max{0,n-(r+1)}<=i <= n)a_i b_(n+m-(r+1)-i) = 0 $
  Which, multiply by $a_n^(r+1)$, since $n-(r+1)<= i<= n$, then $n<= r+1+i<= n+r+1$, hence the coefficient $b_(m-(r+1+i-n))$ has $0 <= r+1+i-n <= r+1$, which for ever index $i$ with this expression being at most $r$, by induction hypothesis, $a_n^(r+1)b_(m-(r+1+i-n)) = 0$, hence every term (besides when the expression is $r+1$) gets annihilated.
  So, eventually we get:
  $ r+1+i-n = r+1 ==> i=n => a_n dot a_n^(r+1) b_(n+m-(r+1-n)) = 0 ==> a_n^(r+2) b_(m-(r+1)) = 0 $
  This completes the induction.
  
  Hence, for $r=m$, we get $a_n^(m+1) b_0 = 0$, because $b_0$ is a unit, then $a_n$ is in fact nilpotent, which $-a_n x^n$ is also nilpotent.

  By @q1, $f- a_n x^n$ is still a unit, and with degree $n-1$. Then, the other non-constnat coefficients can be proven to be nilpotent by induction.


  \ 

+ $==>:$ If $f$ is nilpotent, then $f^k = (a_0+a_1x+...+a_n x^n)^k=0$ for some $k in NN$. Which, the leading term is $a_n^k (x^n)^k = 0$, hence $a_n^k = 0$, or $a_n$ is nilpotent. Since $a_n x^n$ is also nilpotent, then $f - a_n x^n$ is nilpotent (with $deg(f-a_n x^n) = n-1$). So, since the base case $f = a_0$ is nilpotent implies $a_0$ is nilpotent, by induction we can show that each $a_i$ is nilpotent.

  $<==:$ If each coefficient is nilpotent, it's obvious that each degree's component is nilpotent (based on the proof above), hence $f$ is the sum of nilpotent elements, which is nilpotent.

  \ 

+ Suppose $f$ is a zero-divisor, then there exists $g = b_0+b_1x+...+b_m x^m$, where $f g = 0$, and here can assume $m$ is the smallest nonnegative integer that achieves this.

  This shows that $a_n b_m = 0$ (the leading coefficient). Hence, if consider $f(a_n g) = a_n(f g)=0$, since if $a_n g$ is nonzero, then it has degree at most $m-1<m = deg(g)$, hence it reaches a contradiction (since $g$ is assumed to be the smallest). Then, $a_n g=0$.

  Therefore, $(f-a_n x^n)g = f g-(a_n g)x^n = 0$, where $f-a_n x^n$ has degree at most $n-1$. Hence, applying induction, we can deduce that for every $a_k$, there exists nonzero polynomials $g_k$, such that $a_k g_k=0$. If multiply the leading coefficients of all $g_k$ together, since each leading coefficient of $g_k$ multiplied with $a_k$ provides $0$, this product annihilates all coefficients of $f$, hence its product with $f$ provides $0$.

  \ 

+ First, recall that all the coefficients of $f g$ are finite sum of productst of the coefficients of $f$ and $g$, hence let $I=(a_0,a_1,...,a_n),\ J=(b_0,b_1,...,b_m)$ represents the ideals of $f$ and $g$'s coefficients respectively, we get that $K$ (the ideal corresponds to $f g$) satisfies $K subset.eq I J$ (since the generators of $K$, the coefficients of $f g$ are inside $I J$).

  $==>:$ To prove the contrapositive, assume either $f$ or $g$ is not primitive, then since either $I$ or $J$ are proper ideals of $R$, we have $K subset.eq I J subset.neq R$, hence since $K$ is proper, $f g$ is not primitive.

  $<==:$ IF $f$ and $g$ are primite, here using $f$ as an example, since there exists $k_0,k_1,...,k_n in R$, such that $k_0 a_0 + k_1 a_1+...+k_n a_n = 1$,

= D//3
#myQuestion[
  Generalize the results in @q2 to polynomial rings with several variables.
]
#text(weight: "bold")[Pf:]

All the setup can be done through induction. For base case $n=1$ it is verified in @q2. Now, if all the statements are true for $n-1$ (where $n in NN$), then since $R[x_1,...,x_n] = K[x_n]$, where $K = R[x_1,...,x_(n-1)]$. Then:
+ $f in K[x_n]$ is a unit $<==>$ constant coefficient $f_0 in K=R[x_1,...,x_(n-1)]$ is unit, and the other coefficients $f_1,...,f_k in K$ are nilpotent. Which, since the constant of $f in R[x_1,...,x_n]$ is provided in $f_0$, while other non-constant terms' coefficients scattered in $f_1,...,f_k$ (and also the non-constant coefficients in $f_1$ as a member of polynomial ring $R[x_1,...,x_(n-1)]$), by induction hypothesis, this happens iff the constant coefficient of $f$ (also the constant coefficient of $f_0$) is unit, while the other terms are nilpotent.

  \ 

+ $f in K[x_n]$ is nilpotent $<==>$ all coefficients $f_0,...,f_k in R[x_1,...,x_(n-1)]$ is nilpotent. Again, by induction hypothesis, all the coefficients of $f_0,...,f_k$ in $R$ (also the coefficients of $f$) must be nilpotent.

  \ 

+ $f in K[x_n]$ is a zero divisor $<==>$ all its coefficients $f_0,...,f_k in R[x_1,...,x_(n-1)]$ all have some $a_0,...,a_k in R$, such that for each index $i$, $a_i f_i = 0$; which, $f$ multiplied by $a_0...a_k$ would make all coefficients $f_i in R[x_1,...,x_(n-1)]$ go to $0$, hence $a=a_0...a_k$ is the desired element with $a f = 0$.
  
  \ 

+ $f g in K[x_n]$ is primitive $<==>$ $f$ and $g$ are primitive in $K[x_n]$. Which, their coefficients in $R[x_1,...,x_(n-1)]$ must have $gcd$ being $1$. However, the $gcd$ of all its coefficients in $R$ also divides all their coefficients in $R[x_1,...,x_(n-1)]$, hence the $gcd$ in $R$ is limited to be $1$.

= D//4
#myQuestion[
  In the ring $R[x]$, the Jacobson radical is equal to the nilradical.
]
#text(weight: "bold")[Pf:]
Let $N$ be the nilradical, and $J$ be the Jacobson radical of $R[x]$. 
Since $J$ is the intersection of all maximal ideals, $N$ is the intersection of all prime ideals, while maximal ideals are prime, then $N subset.eq J$ ($N$ could be the intersection of more ideals, since prime is not necessarily maximal).

\ 

Now, if $f in J$, by definition $1-f$ is a unit. This happens $<==>$ every non-constant coefficients of $1-f$ is nilpotent (they are given by $-a_1,...,-a_n$, the negaitve non-constant coefficients of $f$), while the constant coefficient of $f$, say $a_0$ satisfies $1-a_0$ being a unit (since $1-a_0$ is the constant coefficient of $1-f$). So, all the non-constant coefficients of $f$ are nilpotent.

Then, since $1-y f$ is also a unit for all $y in R[x]$, consider $y=1+x$: The polynomial $(1+x)f$ is given as follow:
$ (1+x)f = a_0 + sum_(i=1)^(n)(a_(i-1)+a_i)x^i + a_n x^(n+1) $
Then, $1-(1+x)f$ has $-(a_0+a_1)$ as the degree 1 coefficient. Since, $1-(1+x)f$ is a unit, this enforces $-(a_0+a_1)$ to be nilpotent; and since $a_1$ is nilpotent, $a_0$ must also be nilpotent (since $"Nil"(R)$ is an ideal, which forms a group under addition).

So, because every coefficients are nilpotent, $f$ is nilpotent, hence $f in N$, showing the other inclusion $J subset.eq N$. 

= D//5
#myQuestion[
  Let $R$ be a ring, and consider $R[[x]]$ (formal power series ring). Show that:
  + $f$ is a unit in $R[[x]] <==>$ $a_0$ is a unit in $R$.
  + If $f$ is nilpotent, then $a_n$ is nilpotent for all $n >= 0$. Is the converse true?
  + $f$ belongs to the Jacobson radical of $R[[x]] <==>$ $a_0$ belongs to the Jacobson radical of $R$.
  + The contraction of a maximal ideal $M$ of $R[[x]]$ is a maximal ideal of $R$, and $M$ is generated by $M^c$ and $x$.
  + Every prime ideal of $R$ is the contraction of a prime ideal of $R[[x]]$.
]
#text(weight: "bold")[Pf:]
+ $==>:$ If $f$ is a unit in $R[[x]]$, there exists $g in R[[x]]$, with $f g = 1$. Then, the constant coefficient $1$ is given by the multiplication ofconstant coefficients of $f$ and $g$, showing that $a_0$ (constant coefficient of $f$) is a unit.

  $<==:$ If $a_0$ is a unit in $R$, our goal is to find $g = sum_(n=0)^(infinity) b_n x^n$, where $f g = 1$.

  First, it's clear that $b_0 = a_0^(-1)$. Now, for $b_1$, since we want the degree 1 coefficient of $f g$ to be $0$, and the degree $1$ coefficient is given b $a_0 b_1 + a_1 b_0$, then set $b_1 = -a_0^(-1) a_1 b_0$, we get the desired result.

  Inductively, when $b_0,...,b_(n-1)$ all have fixed expression using the collections of $a_n$, since degree $n$ coefficient of $f g$ is given by $sum_(i=0)^(n)a_i b_(n-i)$, then if we want the expression to be $0$, we can set $b_n$ as follow:
  $ a_0 b_n + sum_(i=1)^(n)a_i b_(n-i) = 0, quad b_n = -a_0^(-1)sum_(i=1)^n a_i b_(n-i) $
  So, there exists an expression of $g$, where $f g = 1$, showing that $f$ is a unit.

  \ 

+ Here, if $f$ is nilpotent, then $f^n = 0$ for some $n in NN$. Then, the constant coefficient becomees $a_0^n = 0$, showing that the constant term is nilpotent. THn, $f-a_0 x^0$ becomes a power series with smallest degree $1$, and is also nilpotent.

  Now, by induction, if proven that the $deg <= n-1$ terms are nilpotent, then subtracting out these terms, we get $f_n = a_n x^n + ...$ is nilpotent. Then, there exists $k in NN$, where $f_n^k = 0$. Then, the smallest degree is $x^(n k)$, with coefficient $a_n^k = 0$. Hence, $a_n$ is also nilpotent. Then by induction, all coefficients are nilpotent.

\ 

3.  $==>:$ suppose $f$ belongs to the Jacobson radical of $R[[x]]$, then for all $g in R[[x]]$ (in particular, can choose $g in R$), satisfies $1-g f$ being a unit in $R[[x]]$, which is achieved only when the constant coefficient is a unit (proven in 1.). So, since its constant coefficient is given by $1-g_0 f_0$, since for all $g_0 in R$ this term is a unit, we have $f_0$ being in the Jacbson radical of $R$.

  $<==:$ Suppose $f_0$ belongs to the Jacobson radical of $R$, then for all $g in R[[x]]$, the term $1-g f$ has constant coefficient $1-g_0 f_0$, which is a unit, hence $1-g f$ is a unit. THis shows that $f$ belongs to the Jacobson Radical of $R[[x]]$.

  \ 

4. Given a projection map $p:R[[x]]arrow.r.twohead R$ that returns the constant coefficient, and $M subset R[[x]]$ is maximal. Then, if consider its contraction $M_c := p(M)$, and the projection map $pi:R arrow.r.twohead R\/M_c$, then the composition becomes $pi compose p:R[[x]] arrow.r.twohead R\/M_c$, where we claim that $ker(pi compose p)=M$:

  First, all $f in M$ satisfies $p(f) in M_c$, so $pi(p(f)) = 0$, which $M subset.eq ker(pi compose p)$; also, if $pi(p(f)) = 0$, it shows that $p(f) in M_c$, which $f in p^(-1)(M_c)$. We know by definition $M subset.eq p^(-1)(M_c)$, and $p^(-1)(M_c)$ is an ideal. Then, by maximality of $M$, either $m=p^(-1)(M_c)$, or $p^(-1)(M_c)=R[[x]]$. However, if the second condition happens, we have $M_c = R$, showing that $1$ has a preimage in $M$ (which turns out that preimage is a unit by 1.), so $M=R$, contradicitng the maximality. Hence, we must have $M=p^(-1)(M_c)$, which also shows that $ker(pi compose p)=M$.

  Hence, by First Isomorphism Theorem, $R\/M_c tilde.equiv R[[x]]\/ker(pi compose p) = R[[x]]\/M$ (which is a field by maximality), hence $M_c subset R$ is maximal.

  Finally, $M subset.eq (M_c,x)$ by definition; to show the other inclusion, it suffices to show that $(x) subset.eq M$; notice that all $f in (x)$ has no constant term, hence for any $g in R[[x]]$, $g f$ also has no constant term, then $1-g f$ has constant term $1$, showing that it's a unit. Hence, $f$ actually belongs to the Jacobson radical of $R[[x]]$ (the intersection of all maximal ideal of $R[[x]]$). With $M$ being maximal, $(x) subset.eq M$, hence for any $m in M_c$ (where $M_c subset M$, since everything beyond constant term can be canceld by $(x)$) and any $g,h in R[[x]]$, with $x dot h in M$, we have $m dot g+x dot h in M$, showing that $(M_c, x)subset.eq M$. Therefore, $M = (M_c, x)$, $M$ is generated by all its element's constant coefficient and $x$.

  \ 

5. Suppose $P subset R$ is a prime ideal, using the same projection map $p$ in part 4, consider $p^(-1)(P) subset R[[x]]$: Again, given projection map $pi:R arrow.r.twohead R\/P$, our goal is to prove $ker(pi compose p)= p^(-1)(P)$.

  It's clear that $p^(-1)(P)subset.eq ker(pi compose p)$ (all $f$ in it has $p(f) in P$, so $pi(p(f))=0$). Then, for all $f$ with $pi(p(f))=0$, we have $p(f) in P$, hence $f in p^(-1)(P)$, this shows that $ker(pi compose p)=p^(-1)(P)$.

  Then, by first isomorphism theorem, since $pi compose p:R[[x]]arrow.r.twohead R\/P$, we have:
  $ R[[x]]\/p^(-1)(P) = R[[x]]\/ker(pi compose p)tilde.equiv R\/P $
  This shows that $p^(-1)(P)$ is a prime ideal, since $R[[x]]\/p^(-1)(P)$ is an integral domain.


= ND//6
#myQuestion[
  A ring $R$ is such that every ideal not contained in the nilradical contains a nonzero idempotent (an elemenet $e$ with $e^2=e != 0$). Prove that the nilradical and the Jacobson radical of $R$ are equal.
]
#text(weight: "bold")[Pf:]

Let $N, J$ represent the niradical and Jacobson radical respectively. It is clear that $N subset.eq J$ by definition. 

To prove that $J subset.eq N$ by contradiction, suppose the contrary that $J subset.eq.not N$, by assumption there exists nonzero $e in J$ with $e^2=e$ (which implies $e$ is not nilpotent, hence $e in.not N$). Which by definition of Jacobson radical, every $k in R$ satisfies $1-k e$ being a unit

= ND//7
#myQuestion[
  Let $R$ be a ring in which every element satisfies $x^n=x$ for some $n > 1$. Show that every prime ideal in $R$ is maximal.
]<q7>
#text(weight: "bold")[Pf:]

First, $"Nil"(R) = (0)$: If $x in "Nil"(R)$, then since there exist $n, k in NN$, with $x^n = x$ and $x^k = 0$ (where we demand $k$ to be the smallest, and $n>1$ by assumption), there are two cases to consider:
+ If $k <= n$, then $x^n = 0$, showing that $x=0$.
+ if $k>n$, then $k = l n + r$ for some $l,r in NN$, and $0 <= r < n$. Which, the following is satisfiesd:
  $ x^k = x^(l n+r) = (x^n)^l dot x^r = x^(l+r) = 0 $
  Notice that $l+r < l n + r = k$ by assumption that $n>1$, so we reach a contradiction (since there exists $l+r<k$, with $x^(l+r)=0$).
Hence, the second case doesn't exist, where the first case shows that $"Nil"(R)=(0)$.

= D//8
#myQuestion[
  Let $R != 0$ be a ring. Show that the set of prime ideals of $R$ has minimal elements with respect to inclusion.
]<q8>
#text(weight: "bold")[Pf:]

We'll prove by Zorn's Lemma, where let $A$ be the set of all prime ideals, and the Partial Order given by  $P_1 succ.eq P_2$ iff $P_1 subset.eq P_2$. 

Let $C subset.eq A$ be a chain, and let $P_C = sect.big_(P in C) P$. It is clear that $P_C$ is an ideal, and if $P_C in A$, then $P_C$ is an upper bound of $C$. So, it suffices to show that $P_C in A$ (or $P_C$ is a prime ideal).

Suppose $x,y in R$ satisfies $x y in P_C$, then since for any prime ideal $P in C$, $x y in P$, then either $x in P$ or $y in P$. If all $P in C$ contains $x$ (or $y$), then we're done. Now, if some contains $x$ and some contains $y$, consider the subchain $C_x := {P in C | x in P}$: 
- If $C_x$ is comaximal in $C$ (in a set theoretic), then for every $P in C$, there exists $P_x in C_x$, where $P_x succ.eq P$, so $P_x subset.eq P$, hence $x in P$, showing that $x in P_C$.
- Else if $C_x$ is not comaximal in $C$, then there exists $P in C$, where all $P_x in C_x$ has $P succ.neq P_x$ (which $P in.not C_x$). Hence, $y in P$, showing that all $P_x in C_x$ has $P subset.neq P_x$, or $y in P_x$. So, given $P in C$, regardless of its containment in $C_x$, we have $y in P$, showing that $y in P_C$.

The above statements show that $P_C$ is prime, hence $P_C in A$, every chain has an upper bound.
Then, by Zorn's Lemma, this POset has a maximal element, which is the minimal elements with respect to inclusion.

= D//9
#myQuestion[
  Let $I subset.neq R$ be an ideal. Show that $I = sqrt(I) <==>$ $I$ is an intersection of prime ideals.
]

$==>:$ If $sqrt(I)=I$, since the projection map $phi:R arrow.r.twohead R\/I$ satisfies the following: 
$ I = sqrt(I) = phi^(-1)("Nil"(R\/I)) = sect.big_(overline(P)subset R\/I "prime")phi^(-1)(overline(P)) = sect.big_(I subset.eq P subset R "prime") P $
Which is an intersection of prime ideals.

\ 

$<==:$ Suppose ${P_i}_(i in Alpha)$ is a collection of prime ideals, and define $I := sect.big_(i in Alpha)P_i$. Then, for all $x in sqrt(I)$, since there exists $n in NN$, with $x^n in I$, because $x^n in P_i$ for all index $i in Alpha$, then $x in P_i$, hence $x in I$, showing that $sqrt(I) subset.eq I$.
Since the other inclusion is trivially true, $sqrt(I)=I$.

= D//10
#myQuestion[
  Let $R$ be a ring, $"Nil"(R)$ be its nilradical. Show that the following are equivalent:
  + $R$ has exactly one prime ideal.
  + Every element of $R$ is either a unit or nilpotent.
  + $R\/"Nil"(R)$ is a field.
]

$1 ==> 2:$ Suppose $R$ has precisely one prime ideal, then since $"Nil"(R)$ is the intersection of all prime ideals, $"Nil"(R) = P$ (the prime ideal). This also enforces $"Nil"(R)$ to be maximal (since every commutative ring has a maximal ideal, and all maximal ideal is prime). 

Now, suppose $u in R \\ "Nil"(R)$ (i.e. not nilpotent), then since $"Nil"(R) subset.neq "Nil"(R) + (u)$, then $"Nil"(R)+(u) = R$, showing that $1 = k u + x$ for some $k in R$ and $x in "Nil"(R)$. Notice that $-x$ is nilpotent, which $1-x$ is a unit, hence $1-x = k u$, showing that $k u$ is a unit, which $u$ is a unit.

Hence, every element of $R$ is either a unit or nilpotent.

\ 

$2 ==> 3:$ Suppose every element is either a unit or nilpotent, then for all $overline(u) in R\/"Nil"(R)$ (with $overline(u) := u mod "Nil"(R)$) that is nonzero, since $u$ is a unit, then inherantly, $overline(u)$ is also a unit in $R\/"Nil"(R)$, showing that it is a field.

\ 

$3==> 1:$ Suppose $R\/"Nil"(R)$ is a field, then $"Nil"(R)$ is maximal. Now, suppose $P$ is a prime ideal, then because $"Nil"(R) subset.eq P subset.neq R$, then this enforces $"Nil"(R) = P$. Hence, there is only one prime ideal, namely $"Nil"(R)$.

= D//11
#myQuestion[
  A ring $R$ is a #emph("Boolean Ring") if $x^2=x$ for all $x in R$. In a boolean ring $R$, show that:
  + $2x := x+x = 0$ for all $x in R$.
  + Every prime ideal $P$ is maximal, and $R\/P$ is a field with two elements.
  + Every finitely generated ideal in $R$ is principal.
]
#text(weight: "bold")[Pf:]

+ For all $x in R$, since $x^2 = x$, we have $x+1=(x+1)^2 = x^2 + 2x + 1 = x+2x+1$, hence after cancellation, $2x = 0$.

+ Based on @q7, since all element $x in R$ has some $n >1$, with $x^n = x$ (in this case, $n=2$), then all prime ideal $P$ is maximal, showing that $R\/ P$ is a field.

  Now, suppose $x in R$ satisfies $overline(x) in R\/ P$ is nonzero, then since $(overline(x))^2 = overline(x)$, then it is a root of the polynomial $y^2 - y in R\/P [y]$. Since this is a UFD, then there exists only two solution, namely $0$ and $1$. because $overline(x) != 0$ by assumption, then $overline(x) = 1$. Hence, $R\/ P tilde.equiv ZZ_2$.

+ We'll approach by induction. Given $I=(x,y)$, consider $z=x+y+x y in I$: We have $x z= x^2+x y + x^2y = x+x y+ x y = x$, and $y z= x y+y^2+x y^2= x y+y+x y = y$. So, $I = (x,y)subset.eq (z)$ (while $(z) subset.eq I$ by definition). Hence, $(z)=I$, showing that $I$ is principal.

  Now, if this is true for $n-1$ generators, for $I=(a_1,...,a_n)$, since $I=(a_1,...,a_(n-1))+(a_n) = (z)+(a_n) = (z,a_n)$ for some $z in (a_1,...,a_(n-1))$, then $I = (z,a_n)=(z')$ for some $z' in I$, showing that $I$ is principal. This completes the induction.

= ND//12
#myQuestion[
  A local ring contains no idempotent other than $0,1$.
]
#text(weight: "bold")[Pf:]

Recall that a local ring $R$ has exactly one maximal ideal, say $M$. Now, suppose $e in R$ is idempotent, then in the residue field $R\/M$, since it is also a root of the polynomial $x^2-x in (R\/M)[x]$, then $e equiv 0 mod M$, or $e equiv 1 mod M$.

For the first case, we have $(1+e)^2 = 1+2e + e^2 = 1+3e$

For the second case, we have $e = 1+m$ for some $m in M$, hence $m = e-1$. Which, $m^2 = e^2 - 2e + 1 = -e+1 = -(e-1) = -m$, showing that $(m^2)^2 = m^2$

= ND//13
#myQuestion[
  About construction of algebraic closure, read it
]

= D//14
#myQuestion[
  In a ring $R$, let $Sigma$ be the set of all ideals in which every element is a zero-divisor. Show that the set $Sigma$ has maximal elements, and that every maximal element of $Sigma$ is a prime ideal. Hence the set of zero-divisors in $R$ is a union of prime ideals.
]
#text(weight: "bold")[Pf:]

Again, we'll proceed with Zorn's Lemma with the partial order being inclusion. Given a chain $C subset.eq Sigma$, consider the following construction of "ideal":
$ I_C = union.big_(I in C)I $
If the above is an ideal containing only zero divisors, it's clear that it is an upper bound of $C$. It only contains zero divisors, because all $I in C$ only contains zero divisors,, and it's an ideal, because the union of a chain of ideals is an ideal.

Hence, $I_C in Sigma$, showing that every chain in $Sigma$ has an upper bound. Then, by Zorn's Lemma, $Sigma$ has a maximal element.

\ 

Now, given that $P in Sigma$ is a maximal element, why is it prime? For all $x,y in R$, suppose $x y in P$, i.e. $x y$ is a zero divisor. Which as a result, either $x$ or $y$ must be a zero divisor.

Which, WLOG, suppose $x$ is a zero-divisor, then $x in P$: If $x in.not P$, then notice that the ideal $(x)+P$ also contains only zero divisors (for all $k in R$ and $p in P$, the element $k x+p$ is a zero-divisor, since there exists $a, b in R$, with $a x = b p = 0$, then multiply by $a b$ provides $0$), so $(x)+P in Sigma$; and $P subset.neq (x)+P$, but this violates the assumption that $P$ is a maximal element in $Sigma$.

Hence, the assumption is false, $x in P$. This demonstrates that $P$ is prime.

= D//15
#myQuestion[
  Let $R$ be a ring and let $X$ be the set of all prime ideals of $R$. For each subset $E$ or $R$, let $V(E)$ denote the set of all prime ideals of $R$ which contain $E$. Prove that:
  + If $I$ is the ideal generated by $E$, then $V(E) = V(I) = V(sqrt(I))$.
  + $V(0) = X, V(1) = emptyset$.
  + If $(E_i)_(i in I)$ is any family of subsets of $R$, then:
  $ V(union.big_(i in I)E_i) = sect.big_(i in I)V(E_i) $
  4. $V(I sect J) = V(I J) = V(I) union V(J)$ for any ideals $I,J$ of $R$.
  These results show that the sets $V(E)$ satisfies the axioms for closed sets in a topological space. The resulting topology is called the #emph("Zariski topology"). THe topological space $X$ is called the #emph("prime spectrum") of $R$, denoted as $"Spec"(R)$.
]
#text(weight: "bold")[Pf:]

+ For all $P in V(E)$, since it contains $E$, it contains $I$, hence $P in V(I)$, showing that $V(E) subset.eq V(I)$; on the other hand, since $E subset.eq I$, any $P' in V(I)$ contains $I$, hence contains $E$. So, $P' in V(E)$, showing $V(I) subset.eq V(E)$, hence the two are the same.

  Now, since for all $P in V(sqrt(I))$, $P$ containing $sqrt(I)$ implies it contains $I$, hence $P in V(I)$, or $V(sqrt(I)) subset.eq V(I)$; then, for any $P' in V(I)$, any $x in sqrt(I)$ satisfies $x^n in I subset.eq P'$, hence $x in P'$ can be derived through induction and the prime ideal property. So, $sqrt(I) subset.eq P'$, showing that $P' in V(sqrt(I))$. Hence, $V(I)subset.eq V(sqrt(I))$, the two are in fact the same.

  \ 

+ For all $P in X$, since $P$ contains $0$ by def, then $P in V(0)$, showing that $X = V(0)$. Now, $V(1) = emptyset$, because if there exists prime ideals are defined to be proper subgroups of $R$ under addition, while an ideal containing $1$ is $R$ itself, so none of the prime ideals can be in $P(1)$.

  \ 

+ Let $(E_i)_(i in I)$ be a family of subests of $R$. For all $P in V(union.big_(i in I)E_i)$, since all $E_i subset.eq P$, then $P in V(E_i)$, hence $P in sect.big_(i in I)V(E_i)$. For the converse, if $P in sect.big_(i in I)V(E_i)$, then all $E_i subset.eq P$, hence $union.big_(i in I)E_i subset.eq P$, showing that $P in V(union.big_(i in I)E_i)$. This finishes both inclusion.

  \ 

+ Since $I J subset.eq (I sect J) subset.eq I,J$, then for all $P in V(I) union V(J)$, it's clear that $P$ contains $I sect J$, hence $P in V(I sect J)$; and all $P' in V(I sect J)$ automatically contains $I J$, hence $P' in V(I J)$. Thos demonstrates $V(I) union V(J) subset.eq V(I sect J) subset.eq V(I J)$.

  Now, for all $P in V(I J)$, the goal is to prove that either $I subset.eq P$ or $J subset.eq P$: Suppose $I subset.eq P$, then we're done. Else, if $I subset.eq.not P$, there exists $x in I \\ P$. Then, for all $y in J$, since $x y in I J subset.eq P$, then with $x in.not P$, we must have $y in P$ due to the properties of prime ideals. Hence, $J subset.eq P$.

  As a result, we must have $P$ containing either $I$ or $J$, hence $P in V(I) union V(J)$, whosing that $P(I J) subset.eq P(I) union P(J)$.

  The above two casees finishes the prove that all are the same.

= ND//16
#myQuestion[
  Draw pictures of prime spectrum of $ZZ, RR, CC[x], RR[x], ZZ[x]$.
]
#text(weight: "bold")[Pf:]

For $ZZ$, all the prime ideals are $p ZZ$, where $p$ is prime. Then, any set $V(E)$ will be all the prime divisors of some elements in $E$. Because the choice of $E$ can be arbitrary, any collection of prime ideals is closed, hence it forms a discrete topology.

\ 

For $RR$ and $CC$, since the only prime ideal is $(0)$, it's the discrete topology.

\ 

For $CC[x]$, since it's an ED, and $CC$ is algebraically closed, all prime ideals are maximal, and must be generated by irreducible polynomials, in $CC$ are all the linear polynomials. This again forms a discrete topology.

\ 

For $RR[x]$, similar concept applies from $CC[x]$, but here there are irreducible polynomials not with linear order.

\ 

For $ZZ[x]$, it is hard, because it's not a PID, so the characterization of prime ideals are more complicated.

= D//17
#myQuestion[
  For each $f in R$, let $X_f$ denote the complement of $V(f)$ in $X = "Spec"(R)$. The sets $X_f$ are open under Zariski Topology. Show that they form a basis of open sets for the Zariski topology, and that:
  + $X_f sect X_g = X_(f g)$.
  + $X_f = emptyset <==> f$ is nilpotent.
  + $X_f = X <==> f$ is a unit.
  + $X_f = X_g <==> sqrt((f))=sqrt((g))$.
  + $X$ is quasi-compact (that is, every open covering of $X$ has a finite sub-covering. The distinction from regular compactness is due to the possibility that $X$ is not Hausdorff, such distinction happens mostly in algebraic geometry).
  + More generally, each $X_f$ is quasi-compact.
  + An open subset of $X$ is quasi-compact $<==>$ it is a finite union of sets $X_f$.
]
#text(weight: "bold")[Pf:]

First to prove that set of $X_f$ forms a basis, it's because of $1.$ that will be proved later (for any point lying in $X_f sect X_g$, since $X_f sect X_g = X_(f g)$ is also a basis element), and $2.$ (where $X_f = X$ iff $f$ is a unit), which the collection not only covers the whole $X$, it also satisfies the other basis axioms.

\ 

1. Given $f,g in R$, then: 
$ X_f sect X_g = X \\ (V(f) union V(g)) = X\\(V((f)) union V((g))) = X\\(V((f)(g))) = X\\(V((f g)))\ = X\\V(f g) = X_(f g) $
2. $X_f = emptyset <==> V(f) = X <==>$ all prime ideals $P$ satisfies $f in P$ $<==>$ $f$ is nilpotent (in the intersection of all prime ideals, the nilradicals).

\ 

3. $X_f = X <==> V(f) = V((f)) = emptyset$. Which, $f$ is a unit implies it's not contained in any prime ideals, hence $V(f) = emptyset$. On the other hand, if $V((f)) = emptyset$, it implies that $(f) = R$ (since all proper ideal of $R$ is contained in some maximal ideal, hence if $f$ is not a unit, there exists maximal ideal $M$, with $(f) subset.eq M$.Then, $M in V(f)$). 

  Hence, $X_f = X$ is equivalent to $f$ being a unit.

4. Notice that $X_f = X_g$ iff $V((f))=V(f) = V(g)=V((g))$.

  Recall that $sqrt(I) = sect.big_(I subset.eq P)P$ (where $P$ runs through all the prime ideals), and such collection of ideals is precisely $V(I)$. Hence, $V(I)=V(J)$ implies $sqrt(I)=sqrt(J)$ (since both are the intersection of $V(I)$). The converse is also true because $V(I) = V(sqrt(I))$, hence $sqrt(I)=sqrt(J)$ implies $V(I)=V(J)$.
  
  So, we conclude that $X_f=X_g$ iff $V((f))=V((g))$ iff $sqrt((f))=sqrt((g))$.

  \ 

5. Given that the set ${X_f}_(f in R)$ forms a basis of the Zariski Topology, it suffices to consider the open covering formed by subset of this basis (since every open set is union of basis elements). supopse a subset $J subset.eq R$ has ${X_f}_(f in J)$ forms an open cover of $X$, then $X = union.big_(f in J)X_f$, hence $V(J) = sect.big_(f in J)V(f) = X \\ (union.big_(f in J)X_f) = emptyset$. 

  Since $V(J) = V((J)) = emptyset$ (where $(J)$ indicates the ideal generated by $J$), this indicates that $(J) = R$ (since every proper ideal is contained in some maximal ideal, then if $(J)$ is proper, $V((J)) != emptyset$). So, there exists $f_1,...,f_n in J$, and $g_1,..,g_n in R$, such that $sum_(i=1)^n g_i f_i = 1$. Hence, $V((f_1,...,f_n)) = V({f_1,...,f_n}) = emptyset$. Then, based on the following equality, we can confirm that $X_(f_i)$ forms an open cover of $X$, hence proving that a finite subcover exists:
  $ V({f_1,...,f_n}) = sect.big_(i=1)^n V(f_i) = X \\ (union.big_(i=1)^n X_(f_i)) = emptyset ==> union.big_(i=1)^n X_(f_i)=X $

\ 

6. To prove that each $X_f$ is compact, consider a subset $J subset.eq R$ such that $X_f subset.eq union.big_(g in J)X_g$: Taking the complement, we get that $V(f) supset.eq sect.big_(g in J)V(g) = V(J)$, so, for every prime ideal with $J subset.eq P$, since $P in V(f)$, we have $f in P$, hence $f in sect.big_(P in V(J))P$, which since $V(J) = V((J)) = V(sqrt((J)))$, such intersection is precisely $sqrt((J))$. Hence, $f in sqrt((J))$.

  So, it implies that for some $g_1,...,g_n in J$, $l_1,...,l_n in R$, and $k in NN$, we have $f^k = l_1 g_1 + ... + l_n g_n$, showing that $f in sqrt((g_1,...,g_n))$. This further implies that $V(sqrt((g_1,...,g_n))) = V({g_1,...,g_n}) = sect.big_(i=1)^n V(g_i) subset.eq V(f)$, then taking the complement, we have $X_f subset.eq union.big_(i=1)^n X_(g_i)$.

  This proves the existence of finite subcover, hence showing that each $X_f$ is compact.

\ 

7.  $<==:$ Any finite union of sets $X_f$ is open and compact (union of open sets is open, and finite union of compact subsets is compact).

  $==>:$ Suppose $U subset.eq X$ is open and quasi-compact, then its complement $X \\ U = V(E)$ for some subset $E subset.eq R$. Then, consider the following equality:
  $ X\\U = V(E) = sect.big_(f in E)V(f) = X\\(union.big_(f in E)X_f) $
  (since $X_f$ is the complement of $V(f)$).

  As a result, we must have $U = union.big_(f in E)X_f$, hence the collection associated to $E$ forms an open cover of $U$, which by compactness, there exists $f_1,...,f_n in E$, such that $U = union.big_(i=1)^n X_(f_i)$, so it is intersection of finite $X_f$'s.

= D//18
#myQuestion[
  Given $X="Spec"(R)$, for any prime ideal $x in X$, one would denote $P_x := x$ (even though $x$ is essentially $P_x$, just for notational purpose). Show that:
  + The set ${x}$ is closed ($x$ is called a "closed point") in $"Spec"(A) <==> $ $P_x$ is maximal.
  + $overline({x}) = V(P_x)$.
  + $y in overline({x}) <==> P_x subset.eq P_y$.
  + $X$ is a $T_0$-space (i.e. if $x,y$ are distinct points of $X$, then either there is a neighborhood of $x$ that doesn't cotain $y$, or a neighborhood of $y$ which doesn't contain $x$).
]
#text(weight: "bold")[Pf:]
1. $<==:$ Suppose $P_x$ is maximal, then since $V(P_x) = {x}$ (since $x$ is a prime ideal containing itself, and any other prime ideal containing it must be itself due to maximality), then ${x}$ is closed.
  $==>:$ Suppose the set ${x}$ is closed, then there exists subset $E subset R$, such that $V(E) = V((E)) = V(sqrt((E))) = {x}$. 

  Which, notice that $sqrt((E)) = x = P_x$ in this case (properties of radicals), hence $V(P_x) = {x}$, showing that the only prime ideal containing itself is itself. This shows that $P_x$ is maximal (if not, then there should be some maximal ideal containing it, and the set $V(P_x)$ would contain more than one element).

  Hence, ${x}$ is closed $<==> P_x$ is maximal.

\ 

2. For any $x in X$,since $P_x = x$, we have $x in V(P_x)$, then by definition, since $overline({x})$ is the smallest closed set containing $x$ while $V(P_x)$ is closed, $overline({x}) subset.eq V(P_x)$.

  Now, let ${C_i := V(E_i) subset.eq X | i in I}$ denotes the collection of all closed subsets of $X$ containing $x$ (where each $E_i subset.eq R$), hence we have $overline({x}) = sect.big_(i in I)V(E_i) = V(union.big_(i in I)E_i)$.

  Notice that by definition, $V(E_i)$ containing $x$ implies that $E_i subset.eq x = P_x$, hence the union $union.big_(i in I)E_i subset.eq P_x$. Which, as a result, $V(P_x) subset.eq V(union.big_(i in I)E_i) = overline({x})$.

  So, this finishes the proof that $V(P_x) = overline({x})$.

\ 

3. Based on 2., we can conclude that $y in overline({x}) = V(P_x) <==> P_x subset.eq y = P_y$.

\ 

4. Given $x,y$ as two distinct points of $X$, there are two cases to consider:

  First (WLOG), if $x subset.eq y$ (which, since $x != y$, we must have $x subset.neq y$), then as a result, we have $x in.not V(y)$ (since $x$ doesn't contain $y$ by definition). Which, take open subset $U = X\\ V(y)$, we have $x in U$; on the other hand, because $y$ contains itself, then $y in V(y)$, hence $y in.not U$, so $U$ satisfies all the desired result.

  Then, if $x subset.eq.not y$, then there exist point $p in x\\y$, so if consider the set $V(p)$, we have $x in V(p)$, yet $y in.not V(p)$. Hence, take the open subset $U = X\\V(p)$, we have $y in U$, yet $x in.not U$.  

\ 

= D//19
#myQuestion[
  A topological space $X$ is said to be #emph("irreducible") if $X != emptyset$ and if every pair of nonempty open sets in $X$ intersets, or equivalently if every nonempty open set is dense in $X$. Show that $X="Spec"(R)$ is irreducible iff the nilradical of $R$ is a prime ideal.
]
#text(weight: "bold")[Pf:]

$==>:$ We'll prove the contrapositive. If $Nil(R)$ is not prime, then there exists $x,y in R\\Nil(R)$, where $x y in Nil(R)$. Then, if consider $V(x), V(y)$, we first have the following:
$ V(x) union V(y) = V((x)) union V((y)) = V((x)(y)) = V((x y)) = V(x y) = V(Nil(R)) = X $
Hence, let $U_x = X\\V(x)$ and $U_y = X\\V(y)$, we have $U_x sect U_y = X\\(V(x) union V(y)) = emptyset$. However, since both $x,y in.not Nil(R)$, this indicates that $V(x),V(y) != X$ (if one is $X$, then every prime ideal contains that element, showing that it's in $Nil(R)$, but this contradicts), so $U_x,U_y != emptyset$.

Since there exists $U_x, U_y != emptyset$, with $U_x sect U_y = emptyset$, then this proves that $X$ is not irreducible.

\ 

$<==:$ Now, suppose that $Nil(R)$ is prime, notice that all prime ideal contains $Nil(R)$, so $V(Nil(R))=X$. Now, given any open subsets $U_1,U_2 subset.eq X$, there exists subsets $E_1,E_2 in R$, where $U_i = X\\V(E_i)$. If assume that $U_1 sect U_2 = emptyset$, then the complement $V(E_1) union V(E_2) = V((E_1)) union V((E_2)) = V((E_1)(E_2)) = V(Nil(R))=X$, this shows that $(E_1)(E_2)$ is contained in all prime ideals, hence $(E_1)(E_2) subset.eq Nil(R)$.

If $V(E_1)=X$, then $V(E_2)=emptyset$; which, if $V(E_1) != X$, then $E_1 subset.eq.not Nil(R)$, there exists $e_1 in E_1 \\ Nil(R)$. Which, since for all $e_2 in E_2$, $e_1 e_2 in (E_1)(E_2) subset.eq Nil(R)$, we have $e_2 in Nil(R)$, showing that $E_2 subset.eq Nil(R)$, or $V(E_2) = X$.

Since in either case, the union of two being $X$ implies one of the closed set is $X$, then that means one of the complement is $emptyset$, hence $U_1 sect U_2 = emptyset$ implies one of them is emptyset, so any two nonempty open subsets must have nontrivial intersection.

= ND//20
#myQuestion[
  Let $X$ be a topological space.
  + If $Y$ is an irreducible subspace of $X$, then the closure $overline(Y)$ of $Y$ in $X$ is irreducible.
  + Every irreducible subspace of $X$ is contaiend in a maximal irreducible subspace.
  + The maximal irreducible subspaces of $X$ are closed and cover $X$. They're called the #emph("irreducible components") of $X$. What are the irreducible components of a Hausdorff space?
  + If $R$ is a ring and $X="Spec"(R)$, then the irreducible components of $X$ are the closed sets $V(P)$, where $P$ is a minimal prime ideal of $R$.
]
#text(weight: "bold")[Pf:]

1. Suppose $Y subset.eq X$ is an irreducible subspace, then for any open subsets $U_1, U_2 subset.eq X$ such that $U_i sect Y != emptyset$, we have $(U_1 sect Y) sect (U_2 sect Y) = (U_1 sect U_2 sect Y) != emptyset$.

  Which, suppose $U_1, U_2$ now have nontrivial intersection with $overline(Y)$, suppose $y_1,y_2 in overline(Y)$ satisfy $y_i in U_i$ for each $i$, there are two cases:
  - First, if $y_i$ is a limit point of $Y$, then every open neighborhood contains a point in $Y$, hence $U_i$ contains some points in $Y$. 
  - Then, if $y_i$ is an isolated point of the set ${y_i} union Y$, then $y_i in Y$ is enforced: suppose $y_i in.not Y$, then by definition, there exists some open neighborhood $U in.rev y_i$, which $U sect Y = emptyset$. However, this implies that $Y subset.eq X\\U$ (which is a closed set), hence $overline(Y)subset.eq X\\U$, which notice that $y_i in.not X\\U$, while $y_i in overline(Y) subset.eq X\\U$, which is a contradiction.

  Hence, if $U_1, U_2$ has nontrivial intersection with $overline(Y)$, they must both have nontrivial intersection with $Y$, hence $(U_1 sect Y)sect(U_2 sect Y) != emptyset$, showing that $U_1 sect U_2 != emptyset$. This proves the irreducibility of $overline(Y)$.

  \ 

2. For this, we'll use Zorn's Lemma: First, let the set $A$ be all the irreducible subspace of $X$ (it is nonempty, because a single point is irreducible, since its only open set is the point and $emptyset$), and equip it with partial order with inclusion $subset.eq$. Then, for any chain $C subset.eq A$, consider the following subset:
  $ Y_C = union.big_(Y in C)Y $
  First, to show that $Y_C in A$, consider any open subsets $U_1, U_2 subset.eq X$ such that $U_i sect Y_C != emptyset$: Since there exists $y_1, y_2 in Y_C$ such that $y_i in U_i$ for each $i$, and there exists $Y_1,Y_2 in C$ such that each $y_i in Y_i$. Then, based on the property of chain, WLOG, assume $Y_1 subset.eq Y_2$, then $y_1, y_2 in Y_2$. Hence, $U_i sect Y_2 != emptyset$ for each $i$, showing that $U_1 sect U_2 != emptyset$ (since $Y_2$ is irreducible). Hence, any two open subsets with nontrivial intersection with $Y_C$, actually intersects, showing that $Y_C$ is irreducible, hence $Y_C in A$.

  Afterward, since $Y_C$ is obviously an upperbound of $C$, then every chain has an upper bound. By Zorn's Lemma, $A$ has a maximal element (which is a maximal irreducible subspace).

\ 

3. First, given $Y subset.eq X$ that is a maximal, since $overline(Y)$ is also irreducible, and $Y subset.eq overline(Y)$, then by maximality, we must have $Y=overline(Y)$, showing that $Y$ is closed.

  Given a Hausdorff space, suppose nonempty $Y subset.eq X$ is an irreducible component of $X$, then $Y = {x}$ for some $x in X$: Suppose the contrary that $Y$ contains $y_1,y_2$ that are distinct, then by Hausdorff definition, there exists open neighborhoods $U_1, U_2subset.eq X$, where each $y_i in U_i$, and $U_1 sect U_2 = emptyset$. 

  However, since each $U_i sect Y != emptyset$ (since it contains $y_i$), by irreducibility we must have $U_1 sect U_2 != emptyset$, which is a contradiction. Hence, $Y$ must be a singleton set.

  This shows that a Hausdorff Space has irreducible components being all the singleton set.

  \ 

4. 