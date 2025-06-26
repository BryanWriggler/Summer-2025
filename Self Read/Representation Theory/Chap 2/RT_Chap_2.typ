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

= D//1
#myQuestion[
  Prove that the set of all inner derivations $"ad"x$, $x in L$, is an ideal of $"Der"(L)$.
]
#text(weight: "bold")[Pf:]

The goal is to show that for all derivation $delta in "Der"(L)$ and $x in L$, the commutator $[delta, "ad"x] = "ad"y$ for some $y in L$.

For all $z in L$, the action of the commutator is as follow:
$ delta("ad"x(z))-"ad"x(delta(z)) = delta([x,z]) - [x,delta(z)] = [delta(x),z]+[x,delta(z)]-[x,delta(z)] = [delta(x),z] $
Hence, $delta compose "ad"x = "ad"(delta(x))$, showing that the set of inner derivations is in fact an ideal of $"Der"(L)$.

= ND//2
#myQuestion[
  Show that $frak("sl")(n, F)$ is precisely the derived algebra of $frak("gl")(n,F)$.
]
#text(weight: "bold")[Pf:]

It is clear that the derived algebra of $frak("gl")(n,F)$ is a subalgebra of $frak("sl")(n,F)$ (since the commutator $A B-B A$ always have trace 0).

Now, we want to show that each basis element of $frak("sl")(n,F)$ is can be derived from $frak("gl")(n,F)$:

= ND//3
#myQuestion[
  Proven that the center of $frak("gl")(n,F)$ is $frak("s")(n,F)$ (all scalar matrices). Prove that $frak("sl")(n,F)$ has center $0$, unless $"char"(F)$ divides $n$, in which case the center is $frak("s")(n,F)$.
]
#text(weight: "bold")[Pf:]

The center of $frak("gl")(n,F)$ is precisely the center of the matrix ring. First, it is clear that $frak("s")(n,F) subset.eq Z(L)$ (set $L := frak("gl")(n,F)$), since scalar matrices commute with every matrix.

Then, suppose $A in Z(L)$, then $A$ commutes with all the matrices, in particular the basis matrices $E_(i j)$ (where $1 <= i,j<=n$). Which, we get the following:
$ A E_(i j) = E_(i j)A $
Notice that the left hand side moves the $i^(t h)$ columns to the $j^(t h)$ columns, while the others are $0$; the right hand side moves the $j^(t h)$ row to the $i^(t h)$ row, while the others are $0$.

Hence, if $j != i$, it provides that only the $(i,j)$ entry of $A E_(i j)$ can be nonzero (since this is the intersection of $j^(t h)$ column and $i^(t h)$ row). Then, $A E_(i j)$ remains the $a_(i i)$ entry, while $E_(i j)A$ remains the $a_(j j)$ entry. So, we get that $a_(i i)=a_(j j)$.

Then, if $i=j$,$A E_(i i)$ is left with the $i^(t h)$ column, while $E_(i i)A$ is left with the $i^(t h)$ row. Hence, only the intersection $a_(i i)$ can be nonzero, while the rest entries must be zero. And, since $i$ is arbitrary, this provides that only the diagonal entries can be nonzero.

Finally, This shows that $A$ is not only a diagonal matrix, but every diagonal entry is the same, hence $A in frak("s")(n,F)$, showing that $Z(L) = frak("s")(n,F)$.

\ 

For $frak("sl")(n,F)$ (where $"char"(F) = 0$ or doesn't divide $n$), since for $i != j$, the basis matrix $E_(i j)$ is contained in it, we can again conclude that all the diagonal entries must be the same using the same logic above, which the restriction on the characteristics enforces all the diagonal entries to be $0$.

Then, suppose $A$ is contained in the center, it must commute with all $E_(i i)-E_((i+1)(i+1))$ (where $i<n$, since this is also part of the basis vectors), which we get:
$ A E_(i i)-A E_((i+1)(i+1)) = E_(i i)A-E_((i+1)(i+1))A $
The left side is left with the $i^(t h)$ column and the negative of $(i+1)^(t h)$ column; the right side on the other hand is left with the $i^(t h)$ row and the negative of $(i+1)^(t h)$ row.

Which, the entries other than the intersections are zero, and the intersections are $a_(i i), a_(i(i+1)), a((i+1)i), a((i+1)(i+1))$ (and two are already $0$ by above). Which, the result provides that $a_(i(i+1)), a_((i+1)i)$ are the negative of themselves, which happens only if they're $0$ (or when $"char"(F) = 2$).

So, we can conclude that for $"char"(F) != 0$ or $2$, and doesn't divide $n$, the center of $frak("sl")(n,F)$ is precisely $0$.

\ 

If $"char"(F)$ divides $n$ (and not equal to $2$), then we have $frak("s")(n,F) subset.eq frak("sl")(n,F)$ (since adding $n$ same entries provides $0$), the above proof enforces any matrix in the center to be a scalar matrix, since we need all diagonal entries to be the same, and non-diagonal entries to be $0$).

\ 

Finally, for special case $"char"(F) = 2$, I haven't htought too much...

= D//4
#myQuestion[
  Show that up to isomorphism, there is a unique Lie algebra over $F$ of dimension $3$, whose derived algebra has dimension $1$ and lies in $Z(L)$.
]
#text(weight: "bold")[Pf:]

First, to show the existence, let $L$ be a $3$-dimensional $F$-vector space, and $x,y,z in V$ be its basis. Define $[x,y]=z$, $[x,z]=[y,z]=0$, and that the operation satisfies both bilinearity$[v,v]=0$ for any basis vector mentioned.

To check Jacobi's identity, it suffices to check for the basis vectors chosen.

For $x,y,z$, since $[x,y]=z$, and other combinations all provides $0$, then every term in the Jacobi's identity would be $0$ or $[z,z]$ (which is again $0$).

For three vectors with only two eleemnts of the vector would always be $0$ (since $[a,[b,b]]+[b,[b,a]]+[b,[a,b]] = [b,[b,a]]-[b,[b,a]] = 0$). So, in general the basis vectors all satisfies Jacobi's identity.

Finally, it lies in the center because $z$ lies in the center (since $z$ acts with $x,y,z$ all provides $0$).

So, such example is a desired Lie algebra.

\ 

To show that it is true up to isomorphism, for every such Lie algebra, we need to find the corresponding basis that acts similar as $x,y,z$.

Suppose $L'$ is such Lie algebra, then there exists $z' in Z(L')$ that spans the center. Now, since $z'$ is a basis of the derived algebra, there must exist $x', y'  in L'$, such that $[x',y']=z'$ (since there exists two nonzero vectors $x_0', y_0'$ with $[x_0', y_0'] = k z'$ for some nonzero $k in F$, then scale by proper factor we can get $x', y'$).

Finally, we just need to show that $x',y',z'$ forms a basis of $L'$: Suppose $a x' + b y' + c z' = 0$, then its action with $x'$ and $y'$ respectively provides that $a=b=0$ (since the bracket of $0$ with $x',y'$ would left with the multiple of $z'$ with coefficient $a,b$ respectively, hence $a,b$ are forced to be $0$), then,since $c z' = 0$, we have $c=0$. So, they indeed form a basis that has the same behavior as the original $x,y,z  in L$, showing that the two are isomorphic.

= D//5
#myQuestion[
  Suppose $dim(L)=3$, and $L=[L,L]$, prove that $L$ must be simple.
]
#text(weight: "bold")[Pf:]

The goal is to show that the only ideal is $0$ and $L$. First, notice that any homomorphism $phi:L arrow.r L'$ (WLOG, say $phi$ is surjective), we also have $[L',L']=L'$ (given $y in L'$, by surjectivity there exists $x in L$, with $phi(x)=y$. Then, since $x = sum_(i=1)^n [a_i,b_i]$ due to the statement $[L,L]=L$, we have $y = sum_(i=1)^n [phi(a_i),phi(b_i)]$, hence $y in [L',L']$, or $L' = [L',L']$). 

Given that $I subset.eq L$ is a nonzero ideal. Suppose the contrary that $I$ is proper, then $I$ is either $1$ or $2$-dimensional. Which, we know $[L\/I, L\/I]=L\/I$ based on the above statement.

\ 

For the case of $dim(I)=1$, since $L\/I$ has dimension $2$, then $[L\/I, L\/I]$ only has dimension at most $1$ (for any basis $x,y$, the derived algebra is only spanned by $[x,y]$), which contradicts the above property, where $[L\/I, L\/I]=L\/I$.

\ 

For the case of $dim(I)=2$, since $L\/I$ has dimension $1$, it is abelian, hence $[L\/I, L\/I]=0$, again this contradicts the property $[L\/I, L\/I]=L\/I$.

So, no matter what case we run into a contradiction, then $I$ can't be proper, showing that $L$ must be simple.

= ND//6
#myQuestion[
  Prove that $frak("sl")(n,F)$ is simple, unless $"char"(F) = 3$.
]