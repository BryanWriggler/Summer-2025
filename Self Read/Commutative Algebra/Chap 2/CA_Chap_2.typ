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
  title: "Commutative Algebra Chap 2",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

//2.15
#myQuestion[
  Let $R,S$ be rings, let $M$ be an $R$-module, $P$ a $S$-module, and $N$ an $(R,S)$-module (where it's simultaneously an $R,S$ module, while $a(x b)=(a x)b$ for all $a in R$, $x in N$, and $b in S$). Then, $M times.circle_(R)P$ is a natural $S$-module, while $N times.circle_S P$ is an $R$-module, and this shows that:
  $ (M times.circle_R N)times_S P tilde.equiv M times.circle_R (N times.circle _S P $
]
#text(weight: "bold")[Pf:]

= D //1
#myQuestion[
  Show that $(ZZ\/m ZZ) times.circle_ZZ (ZZ\/n ZZ)=0$, if $m,n$ are coprime.
]
#text(weight: "bold")[Pf:]

Given that $m,n$ are coprime, then there exists $s,t in ZZ$ such that $m s+t n = 1$. Hence, we get the following for any $x times.circle y$ in the tensor module:
$ x times.circle y = (m s+t n)(x times.circle y) = (m s)(x times.circle y) + (t n)(x times.circle y) = s(m x times.circle y) + t(x times.circle n y) $
$  = s(0 times.circle y) + t(x times.circle 0) = 0 $
Since $2(0 times.circle y) = (2 dot 0 times.circle y) = 0 times.circle y$, hence we get $o times.circle y=0$ in general (and vice versa for second entry being $0$).

Hence, all element of this module is $0$.

= D //2
#myQuestion[
  Let $A$ be a ring, $a$ an ideal, $M$ an $A$-module. show that $(A\/a) times.circle_A M$ is isomorphic to $M\/a M$ (Tensor the exact sequence $0 arrow.r a arrow.r A arrow.r A\/a arrow.r 0$ with $M$).
]

#text(weight: "bold")[Pf:]

Given the exact sequence, tensor it with $M$, it forms the following exact sequence:
$ a times.circle M arrow.r A times.circle M arrow.r (A\/a) times.circle M arrow.r 0 $
Which, since $M tilde.equiv A times.circle M$ by $m arrow.r.bar 1 times.circle m$, then by suitable modification one gets the map $a times.circle M arrow.r A times.circle M arrow.r.tilde M$ by $r times.circle m arrow.r.bar r times.circle m arrow.r.bar r dot m in a M$, and this is definitely surjective, so it creates an exact sequence $a times.circle M arrow.r M arrow.r (A\/a)times.circle M arrow.r 0$, such that the first map has image being precisely $a M$. Then, by exactness, the second map is surjective, with kernel being precisely the image of the previous map, or $a M$, hence showing that $(A\/a) times.circle M tilde.equiv M \/ a M$.


= ND //3
#myQuestion[
  Let $A$ be a local ring (i.e. a ring with only one maximal ideal), $M$ and $N$ are finitely generated $A$-modules. Prove that if $M times.circle N=0$, then $M=0$ or $N=0$.
]

#text(weight: "bold")[Pf:]

Let $m$ be the maximal ideal of $A$, then $k=A\/m$ is the residue field. Given that $M_k := k times.circle_A M = (A\/m) times.circle_A M tilde.equiv M\/m M$ based on the previous exercises.

By Nakayama's lemma, $M_k=0$ implies $M=0$. And, if $M times.circle_A N=0$, it implies $(M times.circle_A N)_k = 0$, which implies $M_k$...

= D //4
#myQuestion[
  Let $M_i (i in I)$ be any family of $A$-modules, and let $M$ be their direct sum. Prove that $M$ is flat $<==>$ each $M_i$ is flat.
]
#text(weight: "bold")[Pf:]

$==>:$ We'll prove the contrapositive. If one of the $M_j$ is not flat, there exists $f:L arrow.r N$ injective, such that $f times.circle 1_j:L times.circle M_j arrow.r N times.circle M_j$ is not injective. As a result after including the domain and codomain into $plus.circle.big_(i in I)(L times.circle M_i)$ and $plus.circle.big_(i in I)(N times.circle M_i)$ respectively, since the coordinate at $M_j$ is not injective, the whole map is not injective.

Hence, with $plus.circle.big_(i in I)(K times.circle M_i) tilde.equiv K times.circle(plus.circle.big_(i in I)M_i) = K times.circle M$, the map $L times.circle M arrow.r N times.circle M$ is not injective, showing $M$ is not flat.

\ 

$<==:$ Suppose each $M_i$ is flat, then for any injective homomorphism $f:L arrow.r N$, we have $f times.circle 1_i:L times.circle M_i arrow.r N times.circle M_i$ being injective also, hence the maps between direct sum $plus.circle.big_(i in I)(L times.circle M_i) arrow.r plus.circle.big_(i in I)(N times.circle M_i)$ is also injective (since it's injective coordinate wise). Then, with $plus.circle.big_(i in I)(L times.circle M_i) tilde.equiv L times.circle (plus.circle.big_(i in I)M_i) = L times.circle M$, we get $L times.circle M arrow.r N times.circle M$ is still injective, showing tensor with $M$ preserves injective maps, hence $M$ is flat.

= D//5
#myQuestion[
  Let $A[x]$ be the ring of polynomials in one indeterminate over a ring $A$. Prove that $A[x]$ is a flat $A$-algebra.
]
#text(weight: "bold")[Pf:]

Since $A[x] = plus.circle.big_(n in NN)A x^n$ as an $A$-module, while each $A x^n tilde.equiv A$ as an $A$-module, which $A[x] tilde.equiv plus.circle.big_(n in NN)A = A^(plus.circle NN)$. So, it suffices to show that $A$ is a flat $A$-module (by using Question 4 from above).

Given any module homomorphism $f:M arrow.r N$ injective, the goal is to proof that $f times.circle id_A:M times.circle A arrow.r N times.circle A$ is injective. Because this map satisfies $f times.circle id_A(m times.circle a) = f(m) times.circle a$, then consider the isomorphism $M arrow.r.tilde M times.circle A$ by $m arrow.r.bar m times.circle 1$, and $N times.circle A arrow.r.tilde N$ by $n times.circle a arrow.r (a dot n)$, the suitable composition with the tensor map yields:
$ M arrow.r M times.circle A arrow.r N times.circle A arrow.r N, quad m arrow.r.bar m times.circle 1 arrow.r f(m) times.circle 1 arrow.r f(m) $
Which, the map is precisely $f$, and with both the left and the right morphisms being isomorphisms, the middle part is necessarily injective. Hence, $f times.circle id_A:M times.circle A arrow.r N times.circle A$ is injective, showing that $A$ is a flat $A$-module.

= D//6
#myQuestion[
  For any $A$-module, let $M[x]$ denote the set of all polynomials in $x$ with coefficients in $M$, which is all expressions of the form $m_0 + m_1 x+...+ m_n x^n$, where each $m_i in M$.

  Define the product of an element of $A[x]$ and an element of $M[x]$ in the way of combining indeterminates (like usual polynomial ring), and scalar multiply the coefficients, show that $M[x]$ is an $A[x]$-module.

  Show that $M[x] tilde.equiv A[x] times.circle_A M$.
]
#text(weight: "bold")[Pf:]

Given $a_0+...+a_n x^n in A[x]$, and $m_0+...+m_k x^k in M[x]$, define scalar multiplication as:
$ (a_0+...+a_n x^n) dot (m_0+...+m_k x^k) = sum_(i=0)^(m+n)(sum_(j+l = i\ j,l in NN\ j <= n, l <= k) a_j dot m_l x^i) $
Then this definition defines a scalar multiplication, since given any $a_n x^n, a_k x^k in A[x]$, and $m_l x^l, m_q x^q in M[x]$, we have the following:
$ (a_n x^n+a_k x^k) dot (m_l x^l + m_q x^q) = (a_n dot m_l) x^(n+l) + (a_n dot m_q) x^(n+q) + (a_k dot m_l) x^(k+l) + (a_k dot m_q)x^(k+q) $
Which demonstrates that such "multiplication" is bilinear if consider single element in $A[x]$, inductively one can deduce such bilinearity with arbitrary degree. With $1 in A[x]$, any $g(x) in M[x]$ has $1 dot g(x)=g(x)$ (since each coefficient is scalar multiplied by $1$).

Finally, given $a_n x^n, a_k x^k in A[x]$ and $m_l x^l in A[x]$, we have:
$ a_n x^n dot (a_k x^k dot m_l x^l) = a_n x^n dot ((a_k dot m_l) x^(k+l)) = a_n dot (a_k dot m_l) x^(n+k+l) = (a_n a_k) dot m_l x^(n+k+l) $
$  = (a_n a_k x^(n+k)) dot m_l x^l = (a_n x^n dot a_k x^k) dot m_l x^l $
Hence, for single element the product in $A[x]$ can be exchagned with scalar multiplication in $M[x]$.

\ 

Given that $M[x] tilde.equiv plus.circle.big_(n in NN)M$ (for each degree it associates with a copy of $M$) as $A$-module, then we get:
$ M[x] tilde.equiv plus.circle.big_(n in NN)M tilde.equiv plus.circle.big_(n in NN)(A times.circle_A M) tilde.equiv (plus.circle.big_(n in NN)A) times.circle_A M tilde.equiv A[x] times.circle_A M $
Which, as $A$-module they're isomorphic (an explicit map $A[x] times.circle_A M arrow.r M[x]$ going backward can be constructed by $(a_0+...+a_n x^n) times.circle m arrow.r.bar (a_0 dot m +...+a_n dot m x^m)$). Then, given that $A[x] times.circle_A M$ has an $A[x]$-module structure (since $A[x]$ is also a ring), if define $f(x) dot (g(x) times.circle m) := (f(x)g(x)) times.circle m$ in $A[x] times.circle_A M$ (as an $A[x]$-module), then such multiplication commutes with the scalar multiplication of $A[x]$ in $M[x]$:
$ (a_0+...+a_n x^n) dot ((b_0+...+b_k x^k) times.circle m) arrow.r.bar (a_0+...+a_n x^n) dot (b_0 dot m +...+b_k dot m x^k) $
$ sum_(l=0)^(n+k)(sum_(i+j = l\ i<=n, j<=k)a_i dot (b_j dot m))x^l = (sum_(l=0)^(n+k)sum_(i+j=l\ i<=n, j<=k)a_i b_j x^l) dot m = ((a_0+...+a_n x^n) dot (b_0+...+b_k x^k)) dot m $
Which the last part gets mapped over by $(f(x) g(x)) times.circle m$, showing that $A[x] times.circle_A M$ as $A[x]$-module has the same structure as $M[x]$, which they're also isomorphic as $A[x]$-module.

= D//7
#myQuestion[
  Let $P$ be a prime ideal in $A$. Show that $P[x]$ is a prime ideal in $A[x]$. If $m$ is a maximal ideal in $A$, is $m[x]$ a maximal ideal in $A[x]$?
]
#text(weight: "bold")[Pf:]

First, given $I subset.eq A$ as an ideal, we'll have $I[x] subset.eq A[x]$ being an ideal (since $I$ is an additive group, hence $I[x]$ is also additive group due to it being a coordinate wise addition; if $(r_0+...+r_n x^n) in I[x]$, each $r_i in I$, hence for any $g(x) in A[x]$, multiplication with each term would absorb coefficients of $g(x)$ into $I$, so the resulting polynomial belongs to $I[x]$).

Which, our goal is to prove $A\/I[x] tilde.equiv A[x]\/I[x]$. Given $I arrow.r.hook A arrow.r.twohead A\/I$, one can also generalize such map to the polynomial rings (mostly as modules) given by $I[x] arrow.r.hook A[x] arrow.r.twohead A\/I[x]$ (where the second map is a coefficient wise projection). Then, given any $f(x) in I[x] subset.eq A[x]$, since all its coefficients are contained in $I$, then after coordinate wise projection, $overline(f(x)) in A\/I[x]$ is $0$ (since each coefficient is congruent to $0$ in $A\/I$).

Also, conversely if $f(x) in A[x]$ has projection $overline(f(x))=0$ in $A\/I[x]$, then all of its coefficients must be in $I$, showing that $f(x) in I[x]$, which demonstrates that $0 arrow.r I[x] arrow.r.hook A[x] arrow.r.twohead A\/I[x]arrow.r 0$ is exact. Hence, as $A$-modules, we get that $A[x]\/I[x] tilde.equiv A\/I[x]$, and because each part is a ring homomorphism, we also get that such isomorphism is done also as a ring.

\ 

Now, given that $P subset.eq A$ is a prime ideal, then $A\/P$ is an integral domain, so is $A\/P[x]$, hence $A[x]\/P[x] tilde.equiv A\/P[x]$ is also an integral domain, showing that $P[x]$ is also a prime ideal.

However, if use $m subset.eq A$ a maximal ideal, $m[x] subset.eq A[x]$ is not maximal, since $A[x]\/m[x] tilde.equiv A\/m[x]$ is not a field.

= ND//8
#myQuestion[

]