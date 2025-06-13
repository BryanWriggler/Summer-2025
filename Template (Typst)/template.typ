#import "@preview/rubber-article:0.3.1": *

#show: article.with(
  show-header: true,
  header-titel: "The Title of the Paper",
  eq-numbering: "(1.1)",
  eq-chapterwise: true
)

#maketitle(
  title: "The Title of the Paper",
  authors: ("Authors Name",),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

//setup different math environments
#let question = thmbox.with(
  variant: "Question",
  color: blue
)

// Some example content has been added for you to see how the template looks like.
= Introduction
hello please show something

= Appendix 1
- John Lee, Introduction to Smooth Manifolds

- Michael Spivak, Calculus of Manifolds
