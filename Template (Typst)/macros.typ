//common syntaxes needed

//algebra
#let Gal = math.upright[Gal] //galois
#let Aut = math.upright[Aut] //automorphism
#let End = math.upright[End] //endomorphism
#let Hom = math.upright[Hom] //homomorphism
#let Mor = math.upright[Mor] //morphism, in general category
#let Nil = math.upright[Nil] //nilradical (ring)
#let Ann = math.upright[Ann] //annihilator (ring/ module)
#let Char = math.upright[char] //characteristics
#let coim = math.upright[coim] //coimage (homological algebra)
#let im = math.upright[im] //image
#let Spec = math.upright[Spec]
#let coker = math.upright[coker]
#let span = math.upright[span] //span in lin alg
#let Orb = math.upright[Orb] //orbit in group theory

//category theory
#let cat(name) = math.sans[name] //general category font command
#let Grp = math.sans[Grp] //cat of group
#let Ab = math.sans[Ab] //cat of abel group
#let Ring = math.sans[Ring] //cat of rings
#let Fld = math.sans[Fld] //cat of field
#let RMod = math.sans[R-Mod] //cat of R-Mod
#let RAlg = math.sans[R-Alg] //cat of R-Alg
#let Vect(k) = $sans(Vect_#k)$ //cat of k-vector space (not sure if this works though)
#let Top = math.sans[Top] //cat of topological spaces
#let hTop = math.sans[hTop] //cat of topological spaces, with homotopic classes of continuous maps
#let Sets = math.sans[Set] //cat of sets
#let Ch(name) = math.sans[Ch(#name)] //cat of chain / cochaincomplex over an abelian category, sometimes also expressed as Kom
#let D(name) = math.sans[D(#name)] //derived category 
#let Met = math.sans[Met] //cat of metric spaces

//lie group/lie algebra
#let GL = math.upright[GL] //general linear
#let SL = math.upright[SL] //special linear
#let U = math.upright[U] //unitary
#let SO = math.upright[SO] //special orthogonal
#let SU = math.upright[SU] //special unitary
#let gl = math.frak[gl] 
#let sl = math.frak[sl]
#let so = math.frak[so]
#let su = math.frak[su]

//analysis
#let Vol = math.upright[Vol] //volume, in the sense of Riemann / Jordan measure
#let m = math.upright[m] //measure
#let Supp = math.upright[Supp] //can also be used as support of a commmutative ring, where it's all prime ideals when locolization is nontrivial

//complex
#let Re = math.upright[Re] //real part
#let Im = math.upright[Im] //imaginary part
#let Res = math.upright[Res] //residue
#let Holo = math.cal[O] //holomorphic / analytic function
#let Mero = math.cal[M] //meromorphic function

//physics
#let br = math.bold[r] //position
#let bv = math.bold[v] //velocity
#let ba = math.bold[a] //acceleration
#let bF = math.bold[F] //force
#let bP = math.bold[P] //momentum
#let bL = math.bold[L] //angular momentum
#let bN = math.bold[N] //torque
#let bw = $bold(omega)$ //angular velocity
#let b0 = math.bold[0] //zero vector
#let be = math.overline[e] //use for special case of standard basis