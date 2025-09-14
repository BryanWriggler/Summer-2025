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
#let char = $"char"$
#let Ann = $"Ann"$
#let Spec = $"Spec"$
#let Supp = $"Supp"$
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

= ND//1
#myQuestion[
  1. Let $M$ be a Noetherian $A$-module and $u:M arrow.r M$ be a module homoomorphism. If $u$ is surjective, then $u$ is an isomorphism.
  2. If $M$ is Artinian and $u$ is injective, then again $u$ is an isomorphism.
]
#text(weight: "bold")[Pf:]

1. If we consider $ker(u^n)$ for all natural number $n$, we can easily deduce the fact that $ker(u) subset.eq ker(u^2) subset.eq ... subset.eq ker(u^n)subset.eq ...$, which forms an ascending chain, hence by property of Noetherian module, there exists $n in NN$, such that $ker(u^n)=ker(u^(n+1))=...=ker(u^(n+k))=...$.

  Now, we'll try and claim that $M=ker(u^n) plus.circle im(u^n)$: First, $M=ker(u^n)+im(u^n)$ is clear, since $u$ is surjective, inductively one can also prove that $u^n$ is surjective for all $n in NN$, hence $im(u^n)=M$; then, to prove that they have trivial intersection, suppose $m in ker(u^n) sect im(u^n)$, then there exists $k in M$, such that $u^n(k) = m$, while simultaneously $u^(2n)(k) = u^n(m) = 0$. However, since $ker(u^n)=ker(u^(2n))$ by our claim, then we must have $k in ker(u^n)$ (since $k in ker(u^(2n))$ now). Therefore, $m=u^n(k)=0$, showing the two submodules have trivial intersection.

  As a consequence, we must have $ker(u^n)=0$, which enforces $ker(u)=0$, showing $u$ is an isomorphism.

\ 

2. For Artinian ring, we'll consider the image instead. One can also deduce the fact that $im(u) supset.eq im(u^2) supset.eq ... supset.eq im(u^n) supset.eq ...$, which forms a descending chain. Hence by property of Artinian module, there also exists $n in NN$, such that $im(u^n)=im(u^(n+1))=...=im(u^(n+k))=...$.

  Now, to prove ...

= D//2
#myQuestion[
  Let $M$ be an $A$-module. If every nonempty set of finitely generated submodules of $M$ has a maximal element, then $M$ is Noetherian.
]
#text(weight: "bold")[Pf:]

We'll approach by contradiction. Suppose every nonempty set of finitely generated submodules of $M$ has a maximal element, but $M$ is not Noetherian, hence there exists a submodule $N subset.eq M$ that is not finitely generated.

Now, consider the following inductive process:
- Choose $x_1 in N$, consider $R x_1$ its submodule (finitely generated).
- Since $N$ is not finitely generated, $R x_1 subset.neq N$, hence there exists $x_2 in N\\ R x_1$. So, $R x_1 subset.neq R x_1+R x_2$.
- Inductively, for each $n in NN$, since one can choose $x_1,...,x_n$ such that $R x_1 subset.neq R x_1+R x_2 subset.neq ... subset.neq sum_(i=1)^n R x_i subset.neq N$, one can choose another $x_(n+1) in N \\ sum_(i=1)^n R x_i$, which $sum_(i=1)^(n+1)R x_i$ is a new component of the strictly ascending chain, but still not $N$ (due to the assumption that $N$ is not finitely generated).

By the above inductive step, we get a chain of finitely generated submodules $R x_1 subset.neq R x_2 subset.neq ... subset.neq sum_(i=1)^n R x_i subset.neq ...$, which forms a total order with inclusion. Then, by the assumption this nonempty collection has a maximal element, yet this maximal element must be a maximum due to the property that our collection is a chain (where inclusion is a total order), hence there exists $k in NN$, such that $sum_(i=1)^k R x_i$ is a maximum of the chain. Yet, by our claim $sum_(i=1)^k R x_i subset.neq sum_(i=1)^(k+1)R x_i$ (due to the choice that $x_(k+1) in.not sum_(i=1)^k R x_i$), this violates the maximality of $sum_(i=1)^k R x_i$, hence we reach a contradiction.

As a consequence, our assumption is false, then $M$ must be Noetherian.

= D//3
#myQuestion[
  Let $M$ be an $A$-module and let $N_1,N_2$ be submodules of $M$. If $M\/ N_1$ and $M\/ N_2$ are Noetherian, so is $M\/(N_1 sect N_2)$. Similarly with Artinian in place of Noetherian.
]
#text(weight: "bold")[Pf:]

Consider the map $f:M arrow.r M\/N_1 plus.circle M\/N_2$ by $f(x) = (x mod N_1, x mod N_2)$. Which, if consider $ker(f)$, it satisfies $M\/ker(f) tilde.equiv im(f) subset.eq M\/N_1 plus.circle M\/N_2$, which since $M\/N_1,M\/N_2$ are Noetherian, so is their direct sum, hence as a submodule of the direct sum, $im(f)$ is also Noetherian.

Now, for given $x in N_1 sect N_2$, it's clear that $f(x)=0$ (since $x equiv 0 mod N_1, x equiv 0 mod N_2$), so $N_1 sect N_2 subset.eq ker(f)$; on the other hand, $x in ker(f)$ implies $f(x)=(x mod N_1, x mod N_2) = 0$, so $x in N_1$ and $x in N_2$, hence $x in N_1 sect N_2$, this shows that $ker(f)=N_1 sect N_2$, so $M\/N_1 sect N_2 tilde.equiv im(f)$ is also Noetherian.

\ 

If replace all claim with Artinian, this proof still works.

= HD//4
#myQuestion[
  Let $M$ be a Noetherian $A$-module and let $I=Ann(M) subset.eq A$ be its annihilator. Prove that $A\/I$ is a Noetherian ring.

  If we replace "Noetherian" by "Artinian" in this result, is it still true?
]
#text(weight: "bold")[Pf:]

Given that $M$ is a Noetherian $A$-module, it is finitely-generated, hence there exists $x_1,...,x_n in M$, where $M = sum_(i=1)^n A x_i$.

Define a map $f:A arrow.r M^(plus.circle n)$ by $f(a) = (a dot x_1,..., a dot x_n)$, this is an $A$-linear homomorphism, hence a module homomorphism. So, since $M$ is Noetherian, so is its finite direct sum $M^(plus.circle n)$, hence $im(f) subset.eq M^(plus.circle n)$ is also Noetherian. Which, $A \/ ker(f) tilde.equiv im(f)$ is also Noetherian.

Finally, given any $a in I = Ann(M)$, since $a dot x_i = 0$ for all index $i$, we have $f(a) = 0$, showing $a in ker(f)$, or $I subset.eq ker(f)$; similarly, for all $b in ker(f)$, since $b dot x_i = 0$ for all index $i$, and with $M$ being generated by $x_1,...,x_n$, we in fact have $b dot m=0$ for all $m in M$, showing $b in Ann(M)=I$, proving that $ker(f)=I$.

So, as a result, $A\/I$ is Noetherian.

\ 

A counterexample of the Artinian case can be given, if one can find a non-finitely-generated Artinian $A$-module: If consider $ZZ[1/p]\/ZZ subset.eq QQ\/ZZ$ (all the $p$-primary component) as $ZZ$-modules, then since $(1/p) subset.neq (1/p^2) subset.neq ... subset.neq (1/p^n) subset.neq ...$ (since as $ZZ$-modules, there's no way one can obtain $1/p^(n+1)$ with integer multiples of $1/p^n$), then this module is not Noetherian. Also, itself is not finitely-generated either (since all finite collections must have a maximum power of scalar multiples of $1/p^n$, where everything beyond $1/p^n$, like $1/p^(n+1)$ cannot be generated).

Yet, on the other hand, it is Artinian (read https://en.wikipedia.org/wiki/Artinian_module#Relation_to_the_Noetherian_condition to get some idea).

Since the only annihilator of $ZZ[1/p]\/ZZ$ is $0$ (for every $n in NN$, if $n$ is not divisible by $p$, then $n/p !=0$; if $n= p^k dot q$ where $q$ is coprime to $p$, then $n dot 1/p^(k+1) = q/p != 0$ either). So, $ZZ\/{0} tilde.equiv ZZ$, where $ZZ$ is not Artinian.

= D//5
#myQuestion[
  A topological space $X$ is said to be #emph[Noetherian] if the open subsets of $X$ satisfy the ascending chain condition (or equivalently, the maximal condition). Since closed subsets are complements of open subsets, it comes to the same thing to say that closed subsets of $X$ satisfy the descending chain condition (or equivalently, the minimal condition). Show that, if $X$ is Noetherian, then every subspace of $X$ is Noetherian, and that $X$ is quasi-compact.
]
#text(weight: "bold")[Pf:]

Suppose $X$ is Noetherian, then for any subset $A subset.eq X$, suppose $A supset.eq C_1 supset.eq C_2 supset.eq... supset.eq C_n supset.eq ...$ are descending chain of closed subsets in $A$ under its subspace topology, then for each index $i in NN$, there exists closed subset $V_i subset.eq X$, such that $C_i = A sect V_i$.

Now, for $i=1$ we have $C_1 = A sect V_1$, for $i=2$ we have $A sect V_2 = C_2 subset.eq C_1 = A sect V_1$, so $(A sect V_2) sect (A sect V_1) = A sect (V_1 sect V_2) = C_2$, where $(V_1 sect V_2) subset.eq V_1$ (and $V_1 sect V_2$ is closed in $X$).
Now, inductively assume that for all $k<i$, we have $C_k = A sect (V_1 sect ... sect V_k)$, then since $A sect V_i = C_i subset.eq C_(i-1) = A sect (V_1 sect ... sect V_(i-1))$, then $C_i = (A sect V_i) sect (A sect (V_1 sect ... sect V_(i-1))) = A sect (V_1 sect ... sect V_i)$, where $(V_1 sect ... sect V_i) subset.eq (V_1 sect ... sect V_(i-1))$ is closed.

With the above property, WLOG we can say there exists a descending chain of closed subsets $X supset.eq V'_1 supset.eq ... supset.eq V'_n supset.eq ...$ such that each $C_i = A sect V'_i$. Then, by the Noetherian condition of $X$, $V'_i$ stabilizes at some $n in NN$, which for $k >= n$, since $V'_k = V'_n$, then $C_k = A sect V'_k = A sect V'_n = C_n$, showing that $C_n$ (as a descending chain of closed subsets under subspace topology of $A$) stabilizes at some point. Hence, $A$ (equipved with subspace topology) is Noetherian.

\ 

To prove that $X$ is quasi-compact (Note: the only distinction from compact is that in some text, they assume compactness endows with an extra condition of the space being Hausdorff), we'll utilize Contradiction. Suppose ${U_i}_(i in I)$ (where $I$ has infinite cardinality) forms an open cover of $X$, but has no finite subcover, then consider the following inductive process:
1. Choose $U_(i_1)$ for some $i_1 in I$.
2. Since $U_(i_1)$ doesn't cover $X$, there exists $x_2 in X\\ U_(i_1)$, while $x_2$ is covered by $U_(i_2)$ for some $i_2 in I$. Hence, $U_(i_1) subset.neq U_(i_1) union U_(i_2)$ 
3. Inductively we found $U_(i_1),...,U_(i_n)$ such that each $union.big_(j=1)^k U_(i_j) subset.neq union.big_(j=1)^(k+1)U_(i_j)$ for all $k<n$. Then, since $union.big_(j=1)^n U_(i_j)$ stil doesn't cover $X$ (since there's no finite subcover of ${U_i}_(i in I)$), there exists $x_(n+1) in X\\ union.big_(j=1)^n U_(i_j)$, which $x_(n+1)$ is covered by $U_(i_(n+1))$ for some $i_(n+1) in I$. So, this again shows $union.big_(j=1)^n U_(i_j) subset.neq union.big_(j=1)^(n+1)U_(i_j)$

Let $V_n = union.big_(j=1)^n U_(i_j)$ (which is open), then we get a strictly ascending chain of open subsets $V_1 subset.neq ... subset.neq V_n subset.neq ...$, but this violates the ascending chain conditione for open subsets of $X$, which is a contradiction. Therefore, our assumption must be false, the given open cover must endow a finite subcover. This proves that $X$ is compact.

= D//6
#myQuestion[
  Prove that the following are equivalent:
  1. $X$ is Noetherian topological space
  2. Every open subspace of $X$ is quasi-compact
  3. Every subspace of $X$ is quasi-compact
]
#text(weight: "bold")[Pf:]

$3 ==> 2:$ By definition all open subspace is a subspace, so it's immediate.

\ 

$2 ==>1:$ Suppose every open subspace of $X$ is quasi-compact, then consider an ascending chain of open subsets $U_1 subset.eq ... subset.eq U_n subset.eq ...$, if we take $V= union.big_(n in NN)U_n$, then the collection ${U_n}_(n in NN)$ forms an open cover of $V$ when viewing $V$ as an open subspace of $X$ (since each $U_n = V sect U_n$). Since $V$ is compact, then there exists a finite subcover, so there exists $n_1 < ... < n_k$ in $NN$, such that $union.big_(i=1)^k U_(n_i) = V$. Which, by ascending chain condition, each $U_(n_i) subset.eq U_(n_k)$, so $V= union.big_(i=1)^k U_(n_k) = U_(n_k)$, hence for any integer $l >= n_k$, since $U_(n_k) subset.eq U_l subset.eq V = U_(n_k)$, we have $U_l = U_(n_k)$, proving that the chain stabilizes.

\ 

$1 ==> 3:$ Suppose $X$ is Noetherian, then for any subspace $A subset.eq X$ and any of its open cover ${U_i}_(i in I)$ (where $A subset.eq union.big_(i in I)U_i$), using the same proof as proving $X$ is compact (assuming contradiction + construction of strictly ascending chain of open subsets), one can also prove that $A$ is compact (or every open cover has a finite subcover).

= D//7
#myQuestion[
  A Noetherian Space is a finite union of irreducible closed subspaces (Hint: Consider the set $Sigma$ of closed subsets of $X$ which are not finite unions of irreducible closed subspaces.) Hence the set of irreducible components of a Noetherian Space is finite.
]
#text(weight: "bold")[Pf:]

We'll prove by contradiction. If we assume that $X$ is not a finite union of irreducible closed subspaces, consider $Sigma$ as the set of closed subsets in $X$ that are not finite unions of irreducible closed subspaces, $Sigma$ is nonempty because $X$ is contained in there, and utilizing $supset.eq$ (reverse inclusion) $Sigma$ is a POset such that every chain (which turns out to be a descending chain of closed subsets in $Sigma$) has an upper bound (due to the condition for descending chain of closed subsets to stabilize). Hence, there is a maximal element, say $V$, such that any other $C in Sigma$ has $C,V$ incomparable, or $C supset.eq V$.

Since $V in Sigma$, it cannot be written as finite union of irreducible closed subspaces, in particular itself is not irreducible, hence there exists $F_1,F_2 subset.neq V$ proper closed subsets, such that $V=F_1 union F_2$. However, since $F_1,F_2$ both violates the maximal condition, then $F_1,F_2 in.not Sigma$, hence they're both finite unions of irreducible closed subspaces. Which, $V=F_1 union F_2$ is also union of finite irreducible closed subspaces, yet this contradicts the assumption that $V in Sigma$.

Hence, our assumption is false, $X$ must be finite union of irreducible closed subspaces, and this enforces there to have finite irreducible components of a Noetherian Space.

= HD//8
#myQuestion[
  If $A$ is a Noetherian ring the $Spec(A)$ is a Noetherian topological space. Is the converse true?
]
#text(weight: "bold")[Pf:]

Suppose $A$ is a Noetherian ring, then any ascending chain of ideals (in particular, any ascending chain of radicals) stabilizes at some point.

Now, consider a descendign chain of closed subsets in  $Spec(A)$, say $V(I_1) supset.eq V(I_2) supset.eq ... supset.eq V(I_n) supset.eq ...$, where each $I_n$ can be assumed to be a radical. Then, for each $n$, $I_n = sect.big_(P in V(I_n))P$, hence $V(I_n) supset.eq V(I_(n+1))$ implies $I_n subset.eq I_(n+1)$, which creates an ascending chain of radicals $I_1 subset.eq ... subset.eq I_n subset.eq...$. By the Noetherian condition of $A$, this chain of ideals stabilizes, hence at some $n in NN$ we have $I_n = I_(n+1)=...$, showing $V(I_n)=V(I_(n+1))=...$.

This shows that all descending chain of closed subsets in $Spec(A)$ stabilizes, hence $Spec(A)$ is a Noetherian topological space. 

\ 

The converse is not directly true with the same proof (since it only proves that ascending chain of radicals stabilizes, not for all ideals). Need more investigation.

= D//9
#myQuestion[
  Deduce from Exercise 8 that the set of minimal prime ideals in a Noetherian ring is finite.
]
#text(weight: "bold")[Pf:]

Using Exercise 7 we know a Noetherian Space has finite irreducible components, hence if $A$ is Noetherian Ring, we have $Spec(A)$ being a Noetherian Space, which has finite irreducible components.

Because each irreducible component corresponds to a minimal prime ideal (and also the converse), hence there must have finite minimal prime ideals.

= ND // 10
#myQuestion[
  If $M$ is a Noetherian module (over an arbitrary ring $A$), then $Supp(M)$ (set of prime ideals $P$ such that localization $M_P!=0$) is a closed Noetherian subspace of $Spec(A)$.
]
#text(weight: "bold")[Pf:]

= ND//11 (Need Chapter 5)

= ND//12
#myQuestion[
  Let $A$ be a ring such that $Spec(A)$ is a Noetherian space. Show that the set of prime ideals of $A$ satisfies the ascending chain condition. Is the converse true?
]
#text(weight: "bold")[Pf:]

Suppose $Spec(A)$ is a Noetherian Space, then for any ascending chain of prime ideals $P_1 subset.eq...subset.eq P_n subset.eq ...$ in $A$, since it creates a descending chain of closed subsets $V(P_1) supset.eq ... supset.eq V(P_n) supset.eq ...$ in $Spec(A)$. By Noetherican condition of $Spec(A)$, this chain stabilizes, hence for some $n in NN$, $V(P_n)=V(P_(n+1))=...$. Since now for any $k in NN$ we have $P_n in V(P_(n)) = V(P_(n+k))$, then $P_(n+k) subset.eq P_n subset.eq P_(n+k)$, showing that $P_n=P_(n+k)$, so the ascending chain of prime ideals do stabilize.

\ 

To see details about the converse, it needs more investigation.