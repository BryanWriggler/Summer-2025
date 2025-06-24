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
  title: "Typst Template",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

= ND//1
#myQuestion[
  Let $L = RR^3$. Define $[x,y]=x times y$ the cross product, and verify that $L$ is a Lie algebra. Write down the structure constnats relative to the usual basis of $RR^3$.
]
#text(weight: "bold")[Pf:]

Cross product is both bilinear and antisymmetric, hence the first two axioms are satisfied. It remains to check the Jacobi's Identity.

Given any $x,y,z in RR^3$, for simplicity convert it to standard basis notation: $x = x_1e_1+x_2e_2+x_3e_3$, and the same for $y,z$. Then, we get the following collection of equations:
$ x times (y times z) =  $

(do the calculation later)

Now, given standard basis $e_1,e_2,e_3$, the structure constant is given by:
$ a_(1 2)^3 = 1, quad a_(2 3)^1 = 1,quad a_(3 1)^2=1 $
The reversion rule applies, and if $a_(i j)^k$ has $k = i$ or $k=j$ or $i=j$, the constant is $0$.

= D //2
#myQuestion[
  Verify that the following equations and those implied by (L1) (L2) define a Lie algebra structure on a three dimensional vector space with basis $(x,y,z)$: $[x,y]=z$, $[x,z]=y$, $[y,z]=0$.
]

Given any $a,b,c,d,e,f in F$, consider the following:
$ [a x+b y+c z, d x+e y+f z] = a e[x,y] + a f[x,z] + b d[y,x] + b f[y,z] + c d[z,x]+ c e[z,y]\ =  (a f-c d)y+(a e - b d)z $
Which, let $a_1,a_2,a_3$ be the components of $u$, $b_1,b_2,b_3$ be the components of $v$, and $c_1,c_2,c_3$ be the components of $w$, we get:
$ [u,[v,w]] = [a_1x+a_2y+a_3z,(b_1c_3-b_3c_1)y+(b_1c_2-b_2c_1)z]\ = a_1(b_1c_2-b_2c_1)y + a_1(b_1c_3-b_3c_1)z $
$ [v,[w,u]] = b_1(c_1a_2-c_2a_1)y + b_1(c_1a_3-c_3a_1)z $
$ [w,[u,v]] = c_1(a_1b_2-a_2b_1)y + c_1(a_1b_3-a_3b_1)z $
Which, adding all three terms, it turns out to be $0$. So, Jacobi's Identity is satisfied, it is a Lie algebra.

= D//3
#myQuestion[
  Given ordered bases ${x=mat(
    0,1;0,0
  ), h=mat(
    1,0;0,-1
  ), y=mat(0,0;
  1,0)}$ be an ordered basis for $frak("sl")(2,F)$. Compute the matrices of $"ad"x, "ad"h$, and $"ad"y$ relative to this basis.
]
#text(weight: "bold")[Pf:]

FIrst, for $"ad"x$, havng the input of $x,h,y$ provides the follow:
$ "ad"x(x) = [x,x]=0 $
$ "ad"x(h) = [x,h] = mat(0,1;0,0)mat(1,0;0,-1)-mat(1,0;0,-1)mat(0,1;0,0) = mat(0,-1;0,0)-mat(0,1;0,0) = -2x $
$ "ad"x(y)=[x,y] = mat(0,1;0,0)mat(0,0;1,0)-mat(0,0;1,0)mat(0,1;0,0) = mat(1,0;0,0)-mat(0,0;0,1) = h $
Which, in the ordered basis, the matrix is given by:
$ cal("M")("ad"x) = mat(0,-2,0;0,0,1;0,0,0) $

For $"ad"h$, the input $x,h,y$ provides:
$ "ad"h(x) = [h,x] = -[x,h] = 2x $
$ "ad"h (h) = [h,h]=0 $
$ "ad"h (y) = [h,y] = mat(1,0;0,-1)mat(0,0;1,0)-mat(0,0;1,0)mat(1,0;0,-1) = mat(0,0;-1,0)-mat(0,0;1,0) = -2y $
Hence, the matrix of $"ad"h$ is provided as:
$ cal("M")("ad"h)=mat(2,0,0;0,0,0;0,0,-2) $

For $"ad"y$, the input $x,h,y$ provides:
$ "ad"y(x) = [y,x] = -[x,y]=-h $
$ "ad"y(h) = [y,h] = -[h,y] = 2y $
$ "ad"y (y) = 0 $
Which, it has the following matrix:
$ cal("M")("ad"y)=mat(0,0,0;-1,0,0;0,2,0) $

= ND//4
#myQuestion[
  Find a linear Lie algebra isomorphic to the nonabelian two dimensional algebra constructed in (1,4) (i.e. $[x,y]=x$, given the basis $x,y in V$).
]

= D//5
#myQuestion[
  Verify the asertions made in (1,2) about $frak("t")(n,F),frak("d")(n,F),frak("n")(n,F)$, and compute the dimension of each algebra, by exhibiting bases.
]
#text(weight: "bold")[Pf:]

$frak("T")(n,F)$ as a set of all upper triangular matrices, is a lie algebra (since multiplication of two upper triangular is upper triangular), and it has dimension $n(n+1)/2$ (all upper triangular entries).

$frak("d")(n,F)$ as a set of all diagonal matrices, is a lie algebra (multiplication of two diagonal matrices is diagonal), and it has dimension $n$ (all $n$ diagonal entries).

$frak("n")(n,F)$ as a set of all strict upper triangular is also a lie algebra based on the same reason, and has dimension $n(n-1)/2$ (all strict upper triangular entries).

= D//6
#myQuestion[
  Let $x in frak("gl")(n,F)$ have $n$ distinct eigenvalues $a_1,...,a_n$ in $F$. Prove that the eigenvalues of $"ad"x$ are precisely the $n^2$ scalars $a_i-a_j$ (need not be distinct).
]
#text(weight: "bold")[Pf:]

Let $v_1,...,v_n in F^n$ be the distinct eigenvectors of $x$, and $u_1,...,u_n in F^n$ be the distinct eigenvectors of $x^T$ corresponding to $a_1,...,a_n$ respectively (in matrix representation). 

This is well-defined, because having $n$ distinct eigenvalues makes $x$ diagonalizable, hence there exists invertible $T in frak("gl")(n,F)$, such that $T x T^(-1) = D$ (diagonal consists of $a_1,...,a_n$), which the transpose $(T^T)^(-1)x^T T^T = D$, showing that $x^T$ is also diagonalizable, with the same eigenvalues. 

Consider the set matrices $lambda_(i j) := v_i u_j^T in frak("gl")(n,F)$ (where $1<= i,j <=n$): The action of $"ad"x$ on them becomes:
$ "ad"x(lambda_(i j)) = [x,lambda_(i j)] = x(v_i u_j^T) - (v_i u_j^T)x = a_i (v_i u_j^T)^T - (x^T u_j v_i^T) = a_i lambda_(i j) - (a_j u_j v_i^T)^T\ = a_i lambda_(i j) - a_j (v_i u_j^T) = (a_i-a_j)lambda_(i j) $
Hence, $a_i-a_j$ is an eigenvalue for all $1 <= i,j <= n$.

= D//7
#myQuestion[
  Let $frak("s")(n,F) subset frak("gl")(n,F)$ denote the scalar matrices (set of scalar multiples of the identity). If $"char"(F) = 0$ or else a prime not dividing $n$, prove that $frak("gl")(n,F) = frak("sl")(n,F) plus.circle frak("s")(n,F)$, with $[frak("s")(n,F),frak("gl")(n,F)] = 0$.
]

#text(weight: "bold")[Pf:]

Since all scalar multiples of identity commutes with all matrices in $frak("gl")(n,F)$, it is clear that $[frak("s")(n,F),frak("gl")(n,F)] = 0$ (since $frak("s")(n,F)$ is in fact the center of $frak("gl")(n,F)$).

\ 

Then, the reason why $frak("gl")(n,F)=frak("sl")(n,F)+frak("s")(n,F)$, is because if $"char"(F) = 0$, or a prime not dividng $n$, then $n in F$ is nonzero. Hence, for any $x in frak("gl")(n,F)$, $tr(x)/n in F$ exists, therefore $x$ can be decomposed as:
$ x = (x-tr(x)/n I)+tr(x)/n I $
Where, $tr(x)/n I in frak("s")(n,F)$, and $x-tr(x)/n I in frak("sl")(n,F)$ because the trace is given by $tr(x) - n dot tr(x)/n = 0$.

\ 

Finally, it is a direct sum, because given $a I in frak("sl")(n,F) sect frak("s")(n,F)$ (where $a in F$), we have $tr(a I) = a dot n = 0$, but since $F$ is a field, and $n != 0$, we must have $a = 0$. Hence, the intersection is in fact only the zero matrix, proving that the two forms a direct sum.

= D//8
#myQuestion[
  Verify the stated dimension of $D_l$ (already done in the notes).
]

= ND//9
#myQuestion[
  When $"char"(F) = 0$, show that each classical algebra $L = A_l,B_l,C_l,D_l$ is equal to $[L,L]$.
]
#text(weight: "bold")[Pf:]

= ND//10
#myQuestion[
  Show that $A_1, B_1, C_1$ are all isomorphic, while $D_1$ is a $1$-dimensional Lie algebra. Show that $B_2$ is isomorphic to $C_2$, and $D_3$ to $A_3$. What can you say about $D_2$?
]

= D//11
#myQuestion[
  Verify that the commutator of two derivations of an $F$-algebra is again a derivation, whereas the ordinary product need not be.
]
#text(weight: "bold")[Pf:]

Suppose $delta, delta' in "Der"(L)$ are two derivations, then for all $u,v in L$, the following is true:
$ delta(delta'(u v)) = delta(delta'(u)v + u delta'(v)) = (delta delta'(u)v + delta'(u)delta(v)) + (delta(u) delta'(v)+u delta delta'(v)) $
Then, the commutator has the following behavior:
$ (delta delta' - delta'delta)(u v) =  (delta delta'(u)v + delta'(u)delta(v)) + (delta(u) delta'(v)+u delta delta'(v))  \ -(delta' delta(u)v + delta(u)delta'(v)) - (delta'(u) delta(v)+u delta' delta(v)) $
$ =(delta delta'-delta'delta)(u) v + u(delta delta'-delta'delta)(v) $
Hence, the commutator of $delta, delta'$ is again a derivation, showing that $"Der"(L)$ is a Lie algebra with commutator.

\ 

As a counterexample of general product (composition), consider the polynomial ring $RR[x,y]$ together with the derivations $partial/(partial x), x partial/(partial y)$ acting on the polynomials $x, y$ respectively:
$ partial/(partial x)(x partial/(partial y)(x y)) = partial/(partial x)(x^2) = 2x $
But, if consider the situation when product rule applies, we get:
$ x dot partial/(partial x)(x partial/(partial y)(y)) + partial/(partial x)(x partial/(partial y)(x))dot y = x+0 = x $
Since the two doesn't match, this example doesn't satisfy product rule, hence general product of two derivations don't necessarily produce a derivation.

= D//12
#myQuestion[
  Let $L$ be a Lie algebra and let $x in L$. Prove that the subspace of $L$ spanned by the eigenvectors of $"ad"x$ is a subalgebra.
]
#text(weight: "bold")[Pf:]

Let $K subset.eq L$ be the subspace of $L$ spanned by the eigenvectors of $"ad"x$. To show that it's closed under the bracket operation, it suffices to show for any two distinct eigenvectors $u,v$ of $"ad"x$ (with eigenvalues $a,b in F$), $[u,v] in K$ (since every vector in $K$ is spanned by fiitely many eigenvectors of $"ad"x$, using bilinearity it can be broken down into multiple brackets of pairs of eigenvectors).

Given that $"ad"x(u) = [x,u]= a u$, and $"ad"x(v) =[x,v]= b v$. Then, if consider the following using Jacobi's Identity:
$ "ad"x([u,v]) = [x,[u,v]] = -[u,[v,x]] - [v,[x,u]] = [u,[x,v]]-[v,a u]\ = [u, b v] + [a u, v] = (a+b)[u,v] $
Hence, $[u,v]$ is also an eigenvector of $"ad"x$, showing that $K$ is closed under bracket operation, hence a subalgebra of $L$.