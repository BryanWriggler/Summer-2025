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

= ND //2
#myQuestion[
  Let $A$ be a ring, $a$ an ideal, $M$ an $A$-module. show that $(A\/a) times.circle_A M$ is isomorphic to $M\/a M$ (Tensor the exact sequence $0 arrow.r a arrow.r A arrow.r A\/a arrow.r 0$ with $M$).
]

#text(weight: "bold")[Pf:]

Given the exact sequence, 

= ND //3
#myQuestion[
  Let $A$ be a local ring (i.e. a ring with only one maximal ideal), $M$ and $N$ are finitely generated $A$-modules. Prove that if $M times.circle N=0$, then $M=0$ or $N=0$.
]

#text(weight: "bold")[Pf:]

Let $m$ be the maximal ideal of $A$, then $k=A\/m$ is the residue field. Given that $M_k := k times.circle_A M = (A\/m) times.circle_A M tilde.equiv M\/m M$ based on the previous exercises.

By Nakayama's lemma, $M_k=0$ implies $M=0$. And, if $M times.circle_A N=0$, it implies $(M times.circle_A N)_k = 0$, which implies $M_k$...

= ND //4
#myQuestion[
  
]