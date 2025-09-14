#import "@preview/rubber-article:0.4.1": *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/fletcher:0.5.5" as fletcher: *

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
  1. If $M$ and $N$ are flat $A$-modules, then so is $M times.circle_A N$.
  2. If $B$ is a flat $A$-algebra and $N$ is a flat $B$-module, then $N$ is flat as an $A$-module.
]
#text(weight: "bold")[Pf:]

1. Given any injective homomorphism $f:K arrow.r L$, given $f times.circle id_(M times.circle_A N):K times.circle (M times.circle N) arrow.r L times.circle (M times.circle N)$, since based on associative isomorphism between multiple tensor product, the is isomorphic to $(f times.circle id_M) times.circle id_N: (K times.circle M) times.circle N arrow.r (L times.circle M) times.circle N$, given that $M$ is a flat $A$-module, then $f times.circle id_M$ is injective; again,with $N$ also being a flat $A$-module, then $(f times.circle id_M) times.circle id_N$ is also injective, hence $f times.circle id_(M times.circle N)$ is also injective, showing that $M times.circle_A N$ is flat.

\ 

2. Given $f:A arrow.r B$ characterizing $B$ as an $A$-algebra, if suppose $B$ is a flat $A$-algebra, then for all injective $A$-module homomorphism $g:K arrow.r L$, one must have $g times.circle id_B: K times.circle_A B arrow.r L times.circle_A B$ being injective.

  Now, given $N$ as a flat $B$-module, the goal is to prove that $g times.circle id_N:K times.circle_B N arrow.r L times.circle_B N$ is injective.

  Which, given $N$ as a bimodule (both $A$ and $B$ due to the fact that $N$ has an $A$-action by $a dot n := f(a) n$, and it is compatible with the $B$-action, due to the fact that $f$ maps $A$ into $B$), hence we get $K times.circle_B N tilde.equiv K times.circle_B (B times.circle_A N)$... (probly need the bimodule exercise)

= D//9
#myQuestion[
    Let $0 arrow.r M' arrow.r M arrow.r M'' arrow.r 0$ be an exact sequence of $A$-modules. If $M'$ and $M''$ are finitely generated, then so is $M$.
  ]
#text(weight: "bold")[Pf:]

Given that $M' arrow.r.hook M$, WLOG can identify $M'$ as a submodule of $M$, hence we have $M\/M' tilde.equiv M''$ based on the exactness of the sequence.

Hence, for all $x in M$, since $x mod M' in M\/M'$ is finitely generated (isomorphic to $M''$ which is finitely generated), then if $M\/M' = sum_(i=1)^n A overline(e_i)$ for $e_1,...,e_n in M$, then for all $x in M$, $overline(x) = sum_(i=1)^n a_i overline(e_i)$ for some $a_i in A$, showing that $x = (sum_(i=1)^n a_i e_i)+k$ for some $k in M'$. 

Also, given that $M'$ is finitely generated, $M' = sum_(j=1)^m A f_j$ for some $f_1,...,f_m in M'$, hence $k = sum_(j=1)^m b_j f_j$ for some $b_j in A$. Then, $x = (sum_(i=1)^n a_i e_i)+(sum_(j=1)^m b_j f_j)$, showing that $M (e_1,...,e_n, f_1,...,f_m)$, which $M$ is finitely generated.

= ND//10
#myQuestion[
  Let $A$ be a ring, $a$ an ideal contained in the Jacobson radical of $A$; let $M$ be an $A$-module and $N$ a finitely generated $A$-module, and let $u:M arrow.r N$ be a homomorphism. If the induced homomorphism $M\/ a M arrow.r N\/a N$ is surjective, then $u$ is surjective.
]
#text(weight: "bold")[Pf:]

Given $M arrow.r N arrow.r N\/a N$, since for all $m in M$, we have $r dot m in a M$ (if $r in a$), which gets mapped to $r dot u(m) in a N subset.eq N$, hence the projection onto $a N$ provides $0$, so $a M$ is contained in the kernel of the given map $M arrow.r N\/a N$, hence using first isomorphism theorem, it induces a map $u':M\/ a M arrow.r N / a N$.

= ND//11
#myQuestion[
  Let $A$ be a nonzero ring. Show that $A^m tilde.equiv A^n ==> m=n$ (let $m$ be a maximl ideal of $A$, and $phi:A^m arrow.r.tilde A^n$ be an isomorphism. Then $1 times.circle phi:(A\/m) times.circle A^m arrow.r (A\/m) times.circle A^n$ defines an isomorphism between vector spaces of dimension $m$ and $n$ over the fild $k=A\/m$, hence $m=n$).

  If $phi:A^m arrow.r A^n$ is surjective, then $m >= n$.
  
  If $phi:A^m arrow.r A^n$ is injective, is it always the case that $m<= n$?
]

= D//12
#myQuestion[
  Let $M$ be a finitely generated $A$-module and $phi:M arrow.r A^n$ a surjective homomorphism. Show that $ker(phi)$ is finitely generated.
]
#text(weight: "bold")[Pf:]

Given $e_1,...,e_n$ as a basis of $A^n$, then there exists $u_1,...,u_n in M$, such that $phi(u_i)=e_i$ respectively. Let $N = sum_(i=1)^n A u_i$ (submodule generated by $u_1,...,u_n$), then since for all $u in M$, we have $phi(u) = sum_(i=1)^n a_i e_i = sum_(i=1)^n a_i phi(u_i) = phi(sum_(i=1)^n a_i u_i)$ for some $a_1,...,a_n in A$, then we get that $u - sum_(i=1)^n a_i u_i in ker(phi)$, showing that $ker(phi)+N = M$ (since $u$ subtracted out some part in $N$ belongs to $ker(phi)$).

Also, if consider $u in ker(phi) sect N$, then we have $u=sum_(i=1)^n a_i u_i$ for some $a_1,...,a_n in A$, and it satisfies:
$ 0= phi(u) = phi(sum_(i=1)^n a_i u_i)=sum_(i=1)^n a_i phi(u_i) = sum_(i=1)^n a_i e_i $
Which, with $e_1,...,e_n$ being a basis, then each $a_i = 0$, showing that $u=0$. Hence, $M = ker(phi) plus.circle N$.

\ 

Now, given $v_1,...,v_m in M$, since each $phi(v_i) = sum_(j=1)^n a_(i j)e_j = phi(sum_(j=1)^n a_(i j) u_j)$, then we claim that the collection ${v_i ' = v_i - sum_(j=1)^n a_(i j)u_j}_(i=1)^m$ in fact generates $ker(phi)$: There's no ambiguity that every of these elements belong to $ker(phi)$ (since both parts of $v_i '$ induce the same output via $phi$). Also, for every $v in ker(phi) subset.eq M$, since there exists $b_1,...,b_m in A$ such that $v = sum_(i=1)^m b_i v_i$ (by the claim that $M$ is finitely generated by $v_1,...,v_m$), then we have the following:
$ 0=phi(v)=sum_(i=1)^m b_i phi(v_i) = sum_(i=1)^m sum_(j=1)^n b_i a_(i j)e_j = phi(sum_(i=1)^m sum_(j=1)^n b_i a_(i j) u_j) $
Hence, we get the following: 
$ v-sum_(i=1)^m sum_(j=1)^n b_i a_(i j)u_j= sum_(i=1)^m b_i v_i - sum_(i=1)^m sum_(j=1)^n b_i a_(i j)u_j = sum_(i=1)^m b_i (v_i - sum_(j=1)^n a_(i j)u_j) = sum_(i=1)^m b_i v_i ' in ker(phi) $

\ 

Finally, since $v$ is solely contained in $ker(phi)$, then its unique representation in $M$ must be solely in $ker(phi)$ (or the representation with part in $N$ being $0$ due to the fact that $ker(phi) plus.circle N=M$), then since the above implies $v = sum_(i=1)^m b_i v_i ' + sum_(i=1)^m sum_(j=1)^n b_i a_(i j)u_j$, with the former belongs to $ker(phi)$ and the latter belongs to $N$, then the second term must be $0$ based on the direct sum argument, showing $v=sum_(i=1)^m b_i v_i '$. This finishes the proof that $ker(phi)$ is generated by $v_1,...,v_m in ker(phi)$, showing it's finitely generated.

= D//13
#myQuestion[
  Let $f:A arrow.r B$ be a ring homomorphism, and let $N$ be a $B$-module. Regarding $N$ as an $A$-module by restriction of scalars, form the $B$-module $N_B = B times.circle_A N$. Show that the homomorphism $g:N arrow.r N_B$ which mapse $y arrow.r.bar 1 times y$ is injective and that $g(N)$ is a direct summand of $N_B$.

  (Define $p:N_B arrow.r N$ by $p(b times.circle y) = b dot y$, and show that $N_B = im(g) plus.circle ker(p)$).
]

#text(weight: "bold")[Pf:]

To prove that $g$ is injective, given that any $y in N$ satisfies $p compose g(y) = p(1 times.circle y)=1 dot y=y$,then $p$ is in fact a left inverse of $g$, hence $g$ is injective.

On the other hand, to prove that $g(N)$ is a direct summand of $N_B$, for all $b times.circle y in N_B$, consider $k = b times.circle y - 1 times.circle (b dot y) in N_B$: We know $b times.circle y = k+1 times.circle(b dot y)$, where $1 times.circle (b dot y)=g(b dot y) in im(g)$. Also, $k$ satisfies the following:
$ p(k)=p(b times.circle y- 1times.circle(b dot y)) = b dot y - 1 dot (b dot y)=0 $
Hence, $k in ker(p)$, showing that $b times.circle y in im(g)+ker(p)$.

Also, if $b times.circle y in im(g) sect ker(p)$, then there exists $y' in N$ satisfying $g(y') = 1 times.circle y' = b times.circle y$, and $p(b times.circle y) = b dot y = 0$, so $0=p(b times.circle y) = p(1 times.circle y') = y'$. So, this shows that $b times.circle y = 1 times.circle y' = 0$. Hence, $im(g) plus.circle ker(p) = N_b$.

= D//14
#myQuestion[
  A partially ordered set $I$ is said to be a #emph[direct set] if for each pair $i,j in I$, there exists $k in I$ such that $i,j <= k$.

  Let $A$ be a ring, let $I$ be a directed set and let $(M_i)_(i in I)$ be a family of $A$-modules indexed by $I$. For each pair $i,j in I$ such that $i<=j$, let $mu_(i j):M_i arrow.r M_j$ be an $A$-module homomorphism, and suppose that the following axioms are satisfied:
  1. $mu_(i i) = id_(M_i)$ for all $i in I$
  2. $mu_(i k) = mu_(j k) compose mu_(i j)$ whenever $i<=j<=k$

  (in other words, this is a diagram based on POset category $I$ in category of $A$-Mod, or a functor $F:I arrow.r "A-Mod"$).

  Then the modules $M_i$ and homomorphisms $mu_(i j)$ form a #emph[direct system] $M=(M_i, mu_(i j))$ over the directed set $I$.

  We shall construct an $A$-module $M$ the #emph[direct limit] of the direct system $M$ (or the colimit of the given functor $F$).

  Let $C = plus.circle.big_(i in I)M_i$, and identify each module $M_i$ with its canonical image in $C$. Let $D$ be the submodule of $C$ generated by all elements of the form $x_i - mu_(i j)(x_i)$ whenever $i<= j$ and $x_i in M_i$. Let $M=C\/D$, and let $mu:C arrow.r M$ be the corresponding projection, and let $mu_i = mu|_(M_i)$.

  (The module $M$ is in some sense identifying all the elements in different families connected by the homomorphisms of the direct system to be the same), where $(M, {mu_i:M_i arrow.r M})$ forms a #emph[direct limit] of the direct system $M$, denoted as $lim_(arrow.r)M_i$. From the construction it's clear that $mu_i = mu_j compose mu_(i j)$, whenever $i<= j$.
]
#text(weight: "bold")[Pf:]

Let's do this in a more categorical sense. Since $I$ as a POset forms a category, then the "functor" $F:I arrow.r "A-Mod"$ by $F(i)=M_i$, and $F(i arrow.r j) = mu_(i j):M_i arrow.r M_j$ forms a functor (since $F(i arrow.r i) = F(id_i) = mu_(i i)=id_(M_i)$, and $F(i arrow.r j arrow.r k) = F(i arrow.r k) = mu_(i k)=mu_(j k) compose mu_(i j) = F(j arrow.r k) compose F(i arrow.r j)$), so the direct limit in this case is to consider the colimit of this functor.

\ 

The defined module $M$ and the related projection satisfies $mu(x_(i) - mu_(i j)(x_(i))) = 0$ for all $i,j in I$, $i<= j$, and $x_i in M_i$, by the quotient relation defined, hence $mu_i(x_i) = mu(x_i) = mu(mu_(i j)(x_i)) = mu_(j)(mu_(i j)(x_i))$, showing that $mu_i = mu_j compose mu_(i j)$. Hence, we form the following commutative diagram:

#diagram($
           M_i = F(i) edge("rr", mu_(i j) = F(i arrow.r j), "->") edge("dr", mu_i, "->") && F(j)=M_j edge("dl", mu_j, "->") \ 
           & M
         $)

This shows that $(M, {mu_i})$ in fact forms a cone over the functor $F$.

\ 

Finally, to verify it's a colimit of $F$, consider another $A$-module $N$ together with morphisms ${rho_i:M_i arrow.r N}$ satisfying $rho_i = rho_j compose mu_(i j)$ whenever $i<= j$ (i.e. swap each $mu_i$ by $rho_i$, and $N$ with $M$ in the above diagram), which $(N, {rho_i})$ forms  a cone of $F$ also, the goal is to verify there is a unique module homomorphism $f:M arrow.r N$, such that each $rho_i = f compose mu_i$ (i.e. the cone factors uniquely through the cone $(M,{mu_i})$, or $(M,{mu_i})$ is an initial cone).

Which, suppose such morphism exists, with  $f,f':M arrow.r N$ both satisfy this property, then for all $x = sum_(j=1)^n overline(x_(i_j)) in M$ (where $overline(x_i):= mu(x_i)=mu_i(x_i)$ for any $i in I$, and $x_i in M_i$), we must have:
$ f(x) = sum_(j=1)^n f(overline(x_(i_j))) = sum_(j=1)^n f compose mu_(i_j)(x_(i_j))=sum_(j=1)^n rho_(i_j)(x_(i_j)) = sum_(j=1)^n f' compose mu_(i_j)(x_(i_j)) = f'(x) $
Hence, $f=f'$ (since $x in M$ is arbitrary), so the map must be unique.

Also, if define $f:M arrow.r N$ by $f(overline(x_i)) = rho_i(x_i)$ for all $i in I$, $x_i in M_i$ (and set it as a module homomorphism), it turns out to be well-defined, and $f compose mu_i(x_i) = rho_i(x_i)$ by definition. Hence, $(M,{mu_i})$ is indeed a colimit of the functor $F$, which we called a "direct limit" in this sense.

= ND//15
#myQuestion[
  In the situation of Exercise 14, show that every element of $M$ can be written in the form $mu_i(x_i)$ for some $i in I$ and some $x_i in M_i$.

  Show also that if $mu_i (x_i)=0$, then there exists $j>=i$, such that $mu_(i j)(x_i)=0$ in $M_j$.
]

#text(weight: "bold")[Pf:]

Given that $I$ is a directed set, then for any $i,j in I$, there exists $k in I$, such that $i,j <= k$. Equivalently, in the collected direct system, there exists morphisms $mu_(i k):M_i arrow.r M_k$ and $mu_(j k): M_j arrow.r M_k$.

Hence, given any $x = sum_(j=1)^n overline(x_(i_j)) in M$ (where each $overline(x_i)=mu_i (x_i)$), there exists $k_(n-1) in I$, such that $i_(n-1),i_n <= k_(n-1)$, hence $mu_(i_(n-1) k_(n-1))(x_(i_(n-1))), mu_(i_n k_(n-1))(x_(i_n)) in M_(k_(n-1))$, showing the following:
$ overline(x_(i_(n-1)))+overline(x_(i_n)) = mu_(i_(n-1))(x_(i_(n-1)))+mu_(i_n)(x_(i_n)) = mu_(k_(n-1)) compose mu_(i_(n-1) k_(n-1))(x_(i_(n-1)))+mu_(k_(n-1)) compose mu_(i_n k_(n-1))(x_(i_n)) $
Hence, it shows that $overline(x_(i_(n-1)))+overline(x_(i_n)) = mu_(k_(n-1))(x_(k_(n-1))) = overline(x_(k_(n-1)))$ for some $x_(k_(-1)) in M_(k_(n-1))$. Which, $x = sum_(j=1)^(n-2)overline(x_(i_j)) + overline(x_(k_(n-1)))$, then proceed by induction we get that there exits $k in I$ and $x_k in M_k$, such that $x = mu_k(x_k)$.

\ 

Now, suppose $mu_i(x_i)=0$, then $x_i in D$, hence there exists $i_1,...,i_n, k_1,...,k_n in I$ (each $i_j <= k_j$), and corresponding $x_(i_j) in M_(i_j)$, such that:
$ x_i = sum_(j=1)^n x_(i_j)-mu_(i_j k_j)(x_(i_j)) $
Then, since inductively one can show there exists $k in I$, such that each $i,i_j,k_j <= k$, hence we get the following:
$ 0=mu_i (x_i) = mu(x_i) = sum_(j=1)^n mu_(i_j)(x_(i_j))-mu_(k_j)(mu_(i_j k_j)(x_(i_j))) = sum_(j=1)^n $