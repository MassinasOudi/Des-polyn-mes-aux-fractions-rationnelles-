#require "zarith.top";;

(* ---------------------------1-----------------------------------------------*)
let q1 = Q.of_string "123456789987654321/5678900987654";;
let q2 = Q.of_string "-67831300097/236543209890003";;
let q = Q.to_string (Q.add q1 q2);;

(* ---------------------------3-----------------------------------------------*)
(* Type Gauss *)
type gauss = {re : Q.t ; im : Q.t};;
type r_gauss =
  Gauss of gauss
  |Indefini;;

(* ---------------------------4-----------------------------------------------*)
let r_zero = Gauss({re = Q.of_int 0; im = Q.of_int 0 });;

(* fonction qui renvoie la partie réelle d'un rationnel de Gauss*)
let re_gauss x = match x with
  | Gauss g -> g.re
  | Indefini -> failwith "Erreur : indefini";;

(* fonction qui renvoie la partie imaginaire d'un rationnel de Gauss*)
let im_gauss x = match x with
  | Gauss g -> g.im
  | Indefini -> failwith "Erreur : indefini";;

(* fonction pour vérifier si un rationnel de Gauss est definie *)
let is_not_indef (x: r_gauss) = match x with
  |Gauss g -> Q.is_real(g.re) && Q.is_real(g.im)
  |_ -> false;;

(* fonction pour vérifier si un rationnel de Gauss est nul *)
let is_zero_gauss (x: r_gauss) = match x with
  | Gauss g -> Q.equal g.re Q.zero && Q.equal g.im Q.zero
  | Indefini -> false;;

(* fonction qui vérifie si deux rationnels de Gauss sont égaux*)
let is_eq_gauss (p:r_gauss) (q:r_gauss) = match p, q with
    |Gauss g, Gauss g' -> g.re = g'.re && g.im = g'.im
    |_ -> false;;

(* fonction pour calculer l'addition de deux rationnels de Gauss*)
let add_gauss (x: r_gauss) (y: r_gauss) : r_gauss =
  match (x, y) with
  | (Gauss g1, Gauss g2) ->
   let g = Gauss { re = Q.add g1.re g2.re; im = Q.add g1.im g2.im }
   in if is_not_indef g then g else Indefini
  | _ -> Indefini;;

(* fonction pour calculer la soustraction de deux rationnels de Gauss*)
let sub_gauss (x: r_gauss) (y: r_gauss) : r_gauss =
  match (x, y) with
  | (Gauss g1, Gauss g2) ->
   let g = Gauss { re = Q.sub g1.re g2.re; im = Q.sub g1.im g2.im }
   in if is_not_indef g then g else Indefini
  | _ -> Indefini;;

(* fonction pour calculer la multiplication de deux rationnels de Gauss*)
let mult_gauss (x: r_gauss) (y: r_gauss) : r_gauss =
  match (x, y) with
  | (Gauss g1, Gauss g2) ->
   let g = Gauss { re = Q.sub(Q.mul g1.re g2.re)(Q.mul g1.im g2.im);
                   im = Q.add (Q.mul g1.re g2.im)(Q.mul g2.re g1.im) }
   in if is_not_indef g then g else Indefini
  | _ -> Indefini;;

(* fonction pour calculer l'opposé d'un rationnel de Gauss*)
let op_gauss (x: r_gauss) : r_gauss = match x with
  |Gauss g -> let g' = {re = Q.neg g.re ; im = Q.neg g.im} in
         (Gauss g')
  | _ -> Indefini;;

(* fonction pour calculer l'inverse d'un rationnel de Gauss*)
let inv_gauss (x: r_gauss) : r_gauss = match x with
  |Gauss g -> let denom = Q.add (Q.mul g.re g.re) (Q.mul g.im g.im)
              in let g' =  Gauss { re = Q.div (g.re) denom ;
                                   im = Q.div (Q.neg g.im) denom}
   in if is_not_indef g' then g' else Indefini
  | _ -> Indefini;;


(* ---------------------------5-----------------------------------------------*)
(* Type Poly *)
type poly = (int*r_gauss) list;;

(* polynome nul *)
let (zero:poly)=[];;

(* fonction purge : (int*float) list -> poly
L'appel purge l renvoie la liste l à laquelle on a enlevé les coefficients
égaux à 0.
*)
let rec purge (l:(int*r_gauss) list): poly = match l with
    |[] -> []
    |(_, x)::q when is_zero_gauss x -> purge q
    |t::q -> t :: (purge q);;

(* fonction multCoeff : poly -> float -> poly
L'appel multCoeff p co renvoie le polynôome p multiplié par le réel co *)
let multCoeff (p:poly) (co:r_gauss) : poly =
   let rec aux p acc = match p with
       | [] -> List.rev(purge acc)
       | (x, c)::q -> aux q ((x, mult_gauss c co) :: acc)
   in aux p [];;

(* fonction add : poly -> poly -> poly
L'appel add p q renvoie la somme des polynômes p et q *)
let rec add (p:poly) (q:poly) : poly = match p, q with
    |([], t) | (t, []) -> t
    |((a, b):: q, (a', c)::q') when a = a' -> if (is_eq_gauss b (op_gauss c) = false) then (a, add_gauss b c):: (add q q')
                                              else add q q'
    |((a, b):: q, (a', c)::q') when a' > a -> (a, b) :: (add q ((a',c)::q'))
    |(q, (a', c)::q') -> (a', c) :: (add q q');;

(* fonction qui construit le rationnel de Gauss x + yi *)
let gauss (x: float) (y:float) : r_gauss = Gauss {re = Q.of_float x; im = Q.of_float y};;

 (*fonction sub : poly -> poly -> poly
L'appel sub p q renvoie la difference du polynôme p  avec le polynôme q *)
let rec sub (p1:poly) (p2:poly) : poly = add p1 (multCoeff p2 (gauss (-1.) 0.));;

(* multXn : poly -> int -> poly
L'appel multXn p m renvoie le polynome X^m*p*)
let rec multXn (p:poly) (m:int) : poly = match p with
  |[] -> []
  |(a, b) :: q -> (a + m, b):: multXn q m;;

(* mult_naive : poly -> poly -> poly
mult_naive p q renvoie la multiplication des polynômes p et q en utilisant
la méthode naïve *)
let rec mult_naive (p1:poly) (p2:poly) : poly = match p1 with
    |[] -> []
    |(a, b)::q -> (add  (multXn (multCoeff p2 b) a) (mult_naive q p2));;

(*choisir_coupure : int -> int -> int
choisir_coupure d1 d2 renvoie la moitié du plus petit entier pair supérieur à
d1 et d2. Cette fonction est utilisée dans l'algorithme de Karatsuba.*)
let choisir_coupure (d1:int)  (d2:int) : int = let d = if d1 > d2 then d1
   else  d2 in if d mod 2 = 0 then d/2 else (d+1)/2;;

(* cut: poly -> i -> poly*poly
cut p i  renvoie la paire de polynôme (p0,p1)
satisfaisant p=p0+X^ip_1 avec deg p0<i.
Cette fonction est utilisée dans l'algorithme de Karatsuba.*)
let rec cut (p:poly) (i:int) : poly*poly = match p with
  | [] -> ([], [])
  | (a, b) :: q -> let (p1, p2) = cut q i in if a < i then ((a , b) :: p1, p2)
                                             else (p1,(a - i, b):: p2);;

(* fonction degre : poly-> int
L'appel degre p renvoie le degré du polynome p
le degré du polynome nul sera noté -1 *)
let rec degre (p:poly):int = match (purge p) with
  |[] -> -1
  |t::[] -> fst t
  |_::q -> degre q;;

(* karatsuba: poly -> poly -> int -> poly
kartsuba p q k renvoie le produit p*q en utilisant la méthode de Karatsuba
si l'un des polynômes a son degré <k alors on utilise la méthode naive*)
let rec karatsuba (p:poly) (q:poly) k = match p,q with
   ([], _)| (_,[]) -> []
  |p, q when degre p < k || degre q < k -> mult_naive p q
  |p, q -> let d = choisir_coupure (degre p) (degre q) in let p0, p1 = cut p d in let q0, q1 = cut q d
        in let a = (karatsuba p0 q0 d) in let b = (karatsuba p1 q1 d)
        in let c = sub(karatsuba (add p0 p1) (add q0 q1) d) (add a b) in add a (add (multXn c d) (multXn b (2*d)));;

(* fonction coeff : poly -> int -> float
L'appel coeff p i renvoie le coefficient de X^i dans le développement
du polynôme p*)
let rec coeff (pol:poly) (n:int):r_gauss = match (purge pol) with
  |[] -> r_zero
  |(n', c)::q  when n' = n -> c
  |_::q -> coeff q n ;;

(* fonction cd: poly->float
L'appel cd p renvoie le coefficient dominant du polynôme p*)
let cd (p:poly) : r_gauss = let q = purge p in coeff q (degre q);;

(* renverse int -> poly -> poly:
renverse k p renvoie le polynome Rev_k(p) (cf algorithme de Newton) *)
let renverse (k:int) (p:poly) : poly =
  let rec aux = function
               |[] -> []
               |(a,b) :: q -> ((-1) * a, b) :: aux q
  in match k with
     | k when k < degre p -> failwith ("impossible de calculer le renverse d'ordre " ^
                           (string_of_int (k)) ^ " d'un polynome de degre " ^ (string_of_int (degre p)))
     | k -> multXn (List.rev(aux p)) k;;

(*moduloXn : poly -> int -> poly
modulo Xn p n renvoie le reste de la division de p par X^n *)
let moduloXn (p:poly) (i:int) : poly =
  let rec aux acc = function
     |[] -> List.rev acc
     |(a, b):: q  when a < i -> aux ((a, b)::acc) q
     |_::q -> aux acc q
  in aux [] p;;

(* fonction qui renvoie le terme constant d'un polynôme p*)
let tConst (p : poly) = match p with
    |(0, a)::_ -> a
    |_ -> r_zero;;

(*inverse_mod : poly -> int -> poly
inverse_mod p m renvoie l'inverse de p modulo X^m en suivant l'algorithme de Newton*)
let inverse_mod (p:poly) (m:int) : poly =
  let rec aux (p':poly) = function
    | i when (i/2) > m -> moduloXn p' m
    | i ->
      let p'' = moduloXn (add p' (karatsuba p' (sub [(0, gauss 1. 0.)] (karatsuba p' p 1)) 1)) (i) in
      aux p'' (2 * i)
  in
  match p with
  |p when tConst p <> (gauss 1. 0.) -> failwith "Impossible de calculer l'inverse d'un polynôme de terme
                                           constant différent de 1 avec la méthode de Newton"
  |[] -> failwith "division par 0"
  | _ -> aux [(0, (gauss 1. 0.))] 1;;

(* div : poly -> poly -> poly
div p1 p2 renvoie un couple de polynome (q,r)
tel que q est le quotient et r le reste de la division de p1 par p2
en utilisant l'inversion de Newton *)
let div (a:poly) (b:poly) : poly*poly = match a, b with
   |([], _) -> ([], [])
   |(_,[])-> failwith"Erreur division par 0"
   |a, b ->let m = degre a in let n = degre b in if (m > n) then let p = multCoeff(renverse n b) (inv_gauss (cd b)) in
           let g = inverse_mod p (m-n+1) in let q = renverse (m-n)(moduloXn (karatsuba (renverse m a) (multCoeff g (inv_gauss (cd b))) 1) (m-n+1))
           in let r = sub a (karatsuba b q 1) in (q, r) else ([], a);;

(* ---------------------------8-----------------------------------------------*)
(* fonction qui renvoie le pgcd des polynomes e et f ainsi que les coefficients
de Bezout avec l'initialisation de a0 b0 a1 b1 et le quotient q*)
let rec bezout e a0 b0 f a1 b1 q = let d = div e f in let r = snd(d) in match purge r with
           | [] -> if degre f = 0 && tConst f <> gauss 1. 0.
                   then (([(0, gauss 1. 0.)]), multCoeff a1 (inv_gauss(tConst f)),  multCoeff b1 (inv_gauss(tConst f)))
                   else  (f, a1, b1)
           | _ -> let a = (sub a0 (karatsuba q a1 1))
                  in let b = (sub b0 (karatsuba q b1 1))
                  in bezout f a1 b1 r a b (fst d);;

(* fonction qui renvoie le pgcd des polynomes e et f ainsi que les coefficients
de Bezout*)
let euclide_etendu e f = match f with
  |[] -> (e, ([(0, gauss 1. 0.)]), ([(0, gauss 0. 0.)]))
  |_ -> bezout e ([(0, gauss 1. 0.)]) ([(0, gauss 0. 0.)])f ([(0, gauss 0. 0.)]) ([(0, gauss 1. 0.)]) (fst (div e f));;

(*----------------------------14----------------------------------------------*)
(* fonction qui fais la division suivant les puissances croissantes des polynomes
 a et b et renvoie le couple (q, r) *)
let div_puiss_croiss a b n =
  let p = inverse_mod b (n+1) in
  let q = moduloXn (karatsuba a p 1) (n+1) in
  let r = sub a (karatsuba b q 1) in
  (q, snd (cut r (n+1)));;

(* ---------------------------16--------------------------------------------- *)
(* fonction qui renvoie la derivé du polynome p *)
let derive p =
  let rec aux p acc =
    match p with
    | [] -> List.rev acc
    | (a, _) :: t when a = 0 -> aux t acc
    | (a, g) :: t ->
        let new_term = (a-1, mult_gauss g (Gauss{re= Q.of_int a; im = Q.zero})) in
        aux t (new_term :: acc)
  in aux p [];;

(* ---------------------------17--------------------------------------------- *)
(* Fonction pour évaluer un polynome en X = 0 *)
let eval_at_zero p = [(0, tConst p)];;

(*calcule n! *)
let fact (n) :float =
  let rec aux acc = function
    | 0 -> float_of_int acc
    | n -> aux (acc * n) (n - 1)
  in aux 1 n;;

(*calcule la i-eme dirive de p *)
let rec derive_i p i = match i with
    |0 -> p
    |i -> derive_i (derive p) (i-1);;

(* calcule le i-eme terme de la formule de Taylor*)
let terme p i = karatsuba (eval_at_zero(derive_i p i))
  (multCoeff(multXn [(0, gauss 1. 0.)] i) (gauss (1./.fact i) 0.)) 1;;

(* la formule de taylor*)
let taylor p =
  let rec aux i acc p =
    if i > degre p then acc
    else aux (i+1) (add acc (terme p i)) p
in aux 0 [] p;;

(* ---------------------------tests-------------------------------------------*)
(* g1 = 3 + 2i *)
let g1 = gauss 3. 2.;;

(* g2 = 1 + 2i *)
let g2 = gauss 1. 2.;;

(*g1 + g2 -> 4 + 4i *)
add_gauss g1 g2;;

(*g1 * g2 -> -1 + 8i *)
mult_gauss g1 g2;;

(* 1/g1 -> 3/13 -2i/13 *)
inv_gauss g1;;

(* Polynome A -> 1 + (3 + 2i)X + (5 + 6i)X^2 *)
let pA = [(0, gauss 1. 0.); (1, gauss 3. 2.); (2, gauss 1. 2.)];;

(* Polynôme B -> 1 + (3 + 4i)X *)
let pB = [(0, gauss 1. 0.); (1, gauss 3. 4.)];;

(* pA + pB -> 2 + (6 + 6i)X + (1 + 2i)X^2 *)
add pA pB;;

(* pA * pB -> 1 + (6 + 6i)X + (2 + 20i)X^2 + (-5 + 10 i)x^3*)
karatsuba pA pB 1;;
mult_naive pA pB;;

(* pA / pB -> Q = (348/625 - 112i/625) + (11/25 + 2i/25)X,
R = (241/65 +112i/625)*)
div pA pB;;

(* euclide pA pB -> PGCD(pA, pB) = 1 + (241/113 - 112i/113)X,
U = (-128/113 + 112i/113),
V = (-115/113 + 30i/113)X *)
let (p, u, v) = euclide_etendu pA pB;;

(* pA / pB "puissance croissantes" de rang 2 ->
Q = 1 + (- 2i)X + (-7 + 8i)X^2,
R = (53 - 4i)*)
let (q, r) = div_puiss_croiss pA pB 2;;

(* pA' -> (3 + 2i) + (2 + 4i)X *)
derive pA;;

(*taylor pA ->  1 + (3 + 2i)X + (5 + 6i)X^2 *)
taylor pA;;
