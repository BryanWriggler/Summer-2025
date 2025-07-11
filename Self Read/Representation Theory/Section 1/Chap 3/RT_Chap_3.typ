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
#let char=$"char"$
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
  title: "Typst Template",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

= D//1
#myQuestion[
  Let $I$ be an ideal of $L$. Then each member of the derived series or descending central series of $I$ is also an ideal of $L$.
]
#text(weight: "bold")[Pf:]

For each $n in NN$, the derived series $I^((n)):= [I^((n-1)),I^((n-1))]$ (where $I^((0))=I$), and the descending central series $I^(n):=[I^(n-1),I]$ (where $I^0=I$ again). We'll approach by induction:

First, for $n=0$, since both represents $I$ (which is assumed to be an ideal), so the statement is true.

Now, suppose for any $k<n$, the two series both provide an ideal, which for all $x in I^((k))$ or $I^(k)$, and $y in L$, we have $[x,y] in I^((k))$ or $I^k$ (depending on which ideal it belongs to). Then, for all $x in I^((n))$ (or $I^n$), for every $y in L$, we need to verify separately:
- For $I^((n))=[I^((n-1)),I^((n-1))]$, there exists $(x_i)_(i<=n), (y_i)_(i<=n) subset I^((n-1))$, where $x = sum_(i=1)^n [x_i,y_i]$. Then the following is true:
  $ [x,y]=sum_(i=1)^n [[x_i,y_i],y]=sum_(i=1)^n -[y,[x_i,y_i]] = sum_(i=1)^n ([x_i,[y_i,y]]+[y_i,[y,x_i]]) $
  By assumption, since $I^((n-1))$ is an ideal, $[y_i,y], [y,x_i] in I^((n-1))$, hence the summation expression of $[x,y]$ is a finite sume of derived elements in $I^((n-1))$, so $[x,y] in I^((n))$, showing that $I^((n))$ is an ideal.

- For $I^n = [I^(n-1),I]$, there exists $(x_i)_(i<=n) in I^(n-1)$ and $(y_i)_(i<=n) in I$, where $x=sum_(i=1)^n [x_i,y_i]$. Then the following is true:
  $ [x,y]=sum_(i=1)^n [[x_i,y_i],y] = sum_(i=1)^n ([x_i,[y_i,y]]+[y_i,[y,x_i]]) $
  Since $y_i in I$, $x_i in I^(n-1)$ and $y in L$, we get $[y_i,y] in I$, and $[y,x_i] in I^(n-1)$. Since each component in the summation is a sum of two elements in $I^(n)$ (since each is a bracket of element from $I$ and another element from $I^(n-1)$), showing that $[x,y] in I^n$.
These shows that the derived series and descending central series of an ideal are still series of ideals.

= D//2
#myQuestion[
  Prove that $L$ is solvable iff there exists a chain of subalgebras $L=L_0 supset L_1 supset ... supset L_k=0$, such that $L_(i+1)$ is an ideal of $L_i$, and each quotient $L_i\/L_(i+1)$ is abelian.
]
#text(weight: "bold")[Pf:]

$==>:$ If $L$ is solvable, take the derived series $L=L^((0)) supset L^((1)) supset...supset L^((k))=0$. For each $i<=k$, since $[L^((i)),L^((i+1))] subset.eq [L^((i)),L^((i))] = L^((i+1))$, then $L^((i+1))$ is an ideal of $L^((i))$. Also, if taking the quotient, for all $x,y in L^((i))$, we get the following:
$ [x mod L^((i+1)), y mod L^((i+1))]=[x,y] mod L^((i+1)) = 0 $
(Note: since $[x,y] in L^((i+1))$ by definition of derived series). Hence $L^((i))\/L^((i+1))$ is abelian.

\ 

$<==:$ Suppose there exists a chain of subalgebras $L=L_0 supset L_1 supset...supset L_k=0$, where $L_(i+1) subset L_i$ is an ideal, and $L_i\/L_(i+1)$ is abelian.

First, if consider $L^((1))= [L,L]$, if $L$ is finite-dimensional, let $L=L_1 plus.circle W$ for some subspace $W$, then $L\/L_1 = L_0\/L_1 = W\/L_1$. Since it is abelian, we get $[W\/L_1, W\/L_1] = W^((1))\/ L_1 = 0$, so $[W,W] subset.eq L_1$.

Hence, we get $L^((1))=[L,L] = [L_1, L_1]+[L_1,W]+[W,L_1]+[W,W] subset.eq L_1$.

Which, inductively we get that $L((i)) subset.eq L_i$ for all $i<= k$, hence with $L_k=0$, $L^((k))=0$, showing that $L$ is solvable.


= D//3
#myQuestion[
  Let $char(F)=2$. Prove that $sl(2,F)$ is nilpotent.
]
#text(weight: "bold")[Pf:]

Given $char(F)=2$, then for all $a in F$, $a=-a$. Then, the basis of $sl(2,F)$ is given by ${mat(1,0;0,1), mat(0,1;0,0), mat(0,0;1,0)}$. If taken the commutator, we get:
$ [mat(1,0;0,1),mat(0,1;0,0)] = mat(1,0;0,1)mat(0,1;0,0)-mat(0,1;0,0)mat(1,0;0,1) = mat(0,1;0,0)-mat(0,1;0,0) = 0 $
$ [mat(0,1;0,0),mat(0,0;1,0)]=mat(0,1;0,0)mat(0,0;1,0)-mat(0,0;1,0)mat(0,1;0,0) = mat(1,0;0,0)-mat(0,0;0,1) = mat(1,0;0,1) $
$ [mat(0,0;1,0),mat(1,0;0,1)]=mat(0,0;1,0)mat(1,0;0,1)-mat(1,0;0,1)mat(0,0;1,0) = mat(0,0;1,0)-mat(0,0;1,0) = 0 $
Hence, we get that $(sl(2,F))^(1)$ is spanned by $mat(1,0;0,1)$, so $(sl(2,F))^1 = Z(sl(2,F))$. As a result, $(sl(2,F))^2 = 0$, showing that it's nilpotent.
= ND//4
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]
=//5
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]
=//6
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]
=//7
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]
=//8
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]
=//9
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]
=//10
#myQuestion[
  hello world
]
#text(weight: "bold")[Pf:]