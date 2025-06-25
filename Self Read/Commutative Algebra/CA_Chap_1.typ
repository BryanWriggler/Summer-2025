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

+ date

  \ 

+ 

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

= ND//5
#myQuestion[
  Let $R$ be a ring, and consider $R[[x]]$ (formal power series ring). Show that:
  + $f$ is a unit in $R[[x]] <==>$ $a_0$ is a unit in $R$.
  + If $f$ is nilpotent, then $a_n$ is nilpotent for all $n >= 0$. Is the converse true?
  + $f$ belongs to the Jacobson radical of $R[[x]] <==>$ $a_0$ belongs to the Jacobson radical of $R$.
  + The contraction of a maximal ideal $M$ of $R[[x]]$ is a maximal ideal of $R$, and $M$ i generated by $M^c$ and $x$.
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

+ 
= ND//6
#myQuestion[
  A ring $R$ is such that every ideal not contained in the nilradical contains a nonzero idempotent (an elemenet $e$ with $e^2=e != 0$). Prove that the nilradical and the Jacobson radical of $R$ are equal.
]
#text(weight: "bold")[Pf:]

Let $N, J$ represent the niradical and Jacobson radical respectively. It is clear that $N subset.eq J$ by definition. 

To prove that $J subset.eq N$ by contradiction, suppose the contrary that $J subset.eq.not N$, by assumption there exists $e in J$ with $e^2=e$. Now, consider the ideal $(e)$:

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

= ND//11
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

+ Suppose $I = (a_1,...,a_n)$ is a finitely generated ideal, we claim that everything is generated by $a_1+...+a_n$.

= ND//12
#myQuestion[
  A local ring contains no idempotent other than $0,1$.
]
#text(weight: "bold")[Pf:]

Recall that a local ring $R$ has exactly one maximal ideal, say $M$. Now, suppose $e in R$ is idempotent, then in the quotient ring $R\/M$ (which is a field), since it is also a root of the polynomial $x^2-x in R\/M[x]$, then $e equiv 0 mod M$, or $e equiv 1 mod M$.

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

For $ZZ$, all the prime ideals are $p ZZ$, where $p$ is prime. Then, any set $V(E)$ will be all the prime divisors of some elements in $E$.

\ 

For $RR$ and $CC$, since the only prime ideal is $(0)$, it's the discrete topology.

\ 

FOr $CC[x]$, since it's an ED, and $CC$ is algebraically closed, all prime ideals are maximal, and must be generated by irreducible polynomials, in $CC$ are all the linear polynomials.

\ 

For $RR[x]$, similar concept applies from $CC[x]$, but here there are irreducible polynomials not with linear order.

\ 

For $ZZ[x]$, it is hard, because it's not a PID. ... NOT done

= ND//17
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

  $==>:$ Suppose $U subset.eq X$ is open and quasi-compact, then its complement $X \\ U = V(E)$ for some subset $E subset.eq R$. Then, if we let $F = R\\E$, we have $V(E union.sq F) = V(E) sect V(F) = V(R) = emptyset$