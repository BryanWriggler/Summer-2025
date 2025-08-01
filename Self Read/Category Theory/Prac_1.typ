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
//category
#let Ob = $"Ob"$


//start document
#maketitle(
  title: "Typst Template",
  authors: ("Zih-Yu Hsieh",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

=//1
#problem[
  Given a category $C$, define $C^(o p)$ such that $ O b(C^(o p)) = Ob(C)$, and for any $A,B in Ob(C^(o p))$, define $Hom_(C^(o p))(A,B) := Hom_C(B,A)$ (i.e. reversing the arrow).

  Show that this makes into a category.
][
  For each $A in Ob(C^(o p))$, it's clear that $Id_A in Hom_C(A,A) = Hom_(C^(o p))(A,A)$.

  Then, given $f in Hom_(C^(o p))(A,B)$ and $g in Hom_(C^(o p))(B,C)$ (which have $f:B arrow.r A$ and $g:C arrow.r B$), then we can define the composition $(g,f)arrow.bar g compose_(C^(o p)) f := f compose g in Hom(C,A) = Hom_(C^(o p))(A,C)$. This composition (which is based on the composition in $C$) is definitely associative.

  Which, based on that, the $Id$ map turns out to be the left and right identity in the right sense.

  Diagramatically, we have the following for $C$:
  
  #diagram(cell-size: 30mm, $

    C edge("r", g, ->) edge("d", f compose g, ->) & B edge("dl", f, ->)\ 
    A
  $)

  and the following for $C^(o p)$:

  #diagram(cell-size: 30mm, $
    C   & B edge("l", g, ->)\ 
    A  edge("u", g compose_(C^(o p)) f, ->) edge("ur",f, ->)
  $)

  Which, it can be viewed as "reversing the arrows" of the diagram.
]

#prob[If $A$ is a finite set, how large is $End_("Set")(A)$?][
  Since as a set, $End_("Set")(A) = A^A$ in terms of functions, then the cardinality is $|A|^(|A|)$.
]

#prob[Can we define a category in the style of ][

]
