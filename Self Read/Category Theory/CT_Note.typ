#import "@preview/rubber-article:0.4.1": *
#import "@preview/ergo:0.1.0": *

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
