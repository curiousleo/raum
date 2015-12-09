signature METRIC = sig
  type t
  val distance: t -> t -> real
end

structure Manhattan2D : METRIC = struct
  type t = int * int
  fun distance (x, y) (x', y') = Real.fromInt (x' - x + y' - y)
end

signature MMTREE = sig
  structure Pivot : METRIC
  type 'a mmtree
  val empty : 'a mmtree
  val insert : Pivot.t * 'a -> 'a mmtree -> 'a mmtree
  val range : Pivot.t -> real -> 'a mmtree -> (Pivot.t * 'a) list
  (*
  val lookup : Pivot.t -> 'a mmtree -> 'a
  *)
end

fun uncurry f (x, y) = f x y

fun take 0 xs      = [([], xs)]
  | take _ []      = []
  | take n (x::xs) =
  let
    val t1 = take (n-1) xs
    val t1 = List.map (fn (l, r) => (x::l, r)) t1
    val t2 = take n xs
    val t2 = List.map (fn (l, r) => (l, x::r)) t2
  in
    t1 @ t2
  end

fun allpairs xs =
  let
    val t2 = take 2 xs
    fun f ((p1::p2::[]), r) = (p1, p2, r)
      | f _                 = raise Match
  in
    List.map f t2
  end

datatype 'a mmnode = Lf of 'a mmleaf
                   | Ex of 'a * 'a * real * 'a mmleaf * 'a mmleaf * 'a mmleaf * 'a mmleaf
                   | In of 'a * 'a * real * 'a mmnode * 'a mmnode * 'a mmnode * 'a mmnode
and 'a mmleaf = Zero | One of 'a | Two of 'a * 'a * real

fun list_leaf Zero = []
  | list_leaf (One x) = [x]
  | list_leaf (Two (x, y, _)) = [x, y]

functor Mmtree (P : METRIC) : MMTREE = struct
  structure Pivot : METRIC = P
  type 'a mmtree = (Pivot.t * 'a) mmnode

  fun intersect_aux p rq pa pb r =
    let
      val da = Pivot.distance p pa
      val db = Pivot.distance p pb
      val r1 = db < rq + r andalso da < rq + r
      val r2 = db + rq >= r andalso da < rq + r
      val r3 = db < rq + r andalso da + rq >= r
      val r4 = db + rq >= r andalso da + rq >= r
    in
      r1 orelse r2 orelse r3 orelse r4
    end

  fun intersect p rq (Lf Zero) = false
    | intersect p rq (Lf (One (pa, _))) = Pivot.distance p pa < rq
    | intersect p rq (Lf (Two ((pa, _), (pb, _), r))) = intersect_aux p rq pa pb r
    | intersect p rq (Ex ((pa, _), (pb, _), r, _, _, _, _)) = intersect_aux p rq pa pb r
    | intersect p rq (In ((pa, _), (pb, _), r, _, _, _, _)) = intersect_aux p rq pa pb r

  val empty = Lf Zero

  fun insert (p, x) (Lf Zero) = Lf (One (p, x))
    | insert (p, x) (Lf (One (pa, a))) =
    let val d = Pivot.distance p pa in
      Lf (Two ((pa, a), (p, x), d))
    end
    | insert (p, x) (Lf (Two ((pa, a), (pb, b), r))) =
    let
      val da = Pivot.distance p pa
      val db = Pivot.distance p pb
    in
      if da < r then
        if db < r then
          Ex ((pa, a), (pb, b), r, (One (p, x)), Zero, Zero, Zero)
        else
          Ex ((pa, a), (pb, b), r, Zero, (One (p, x)), Zero, Zero)
      else
        if db < r then
          Ex ((pa, a), (pb, b), r, Zero, Zero, (One (p, x)), Zero)
        else
          Ex ((pa, a), (pb, b), r, Zero, Zero, Zero, (One (p, x)))
    end
    | insert (p, x) (Ex ((pa, a), (pb, b), r, l1, l2, l3, l4)) =
    (* Semi-balancing *)
    let
      val ls = (pa, a) :: (pb, b) :: List.concat (List.map list_leaf [l1, l2, l3, l4])
    in
      if List.length ls > 8 then
        insert (p, x) (In ((pa, a), (pb, b), r, Lf l1, Lf l2, Lf l3, Lf l4))
      else
        let
          val ps = allpairs ls
          fun two (pa, a) (pb, b) = Lf (Two ((pa, a), (pb, b), Pivot.distance pa pb))
          fun ins (a, b, other) = List.foldr (uncurry insert) (two a b) other
          val ts = List.map ins ps
          fun is_ex (Ex _) = true
            | is_ex _      = false
        in
          case List.filter is_ex ts of
            (t::_) => t
          | []     => insert (p, x) (In ((pa, a), (pb, b), r, Lf l1, Lf l2, Lf l3, Lf l4))
        end
    end
    | insert (p, x) (In ((pa, a), (pb, b), r, n1, n2, n3, n4)) =
    let
      val da = Pivot.distance p pa
      val db = Pivot.distance p pb
    in
      if da < r then
        if db < r then
          In ((pa, a), (pb, b), r, insert (p, x) n1, n2, n3, n4)
        else
          In ((pa, a), (pb, b), r, n1, insert (p, x) n2, n3, n4)
      else
        if db < r then
          In ((pa, a), (pb, b), r, n1, n2, insert (p, x) n3, n4)
        else
          In ((pa, a), (pb, b), r, n1, n2, n3, insert (p, x) n4)
    end

  fun range p rq (Lf Zero) = []
    | range p rq (Lf (One (pa, a))) =
    if Pivot.distance p pa < rq then [(pa, a)] else []
    | range p rq (Lf (Two ((pa, a), (pb, b), _))) =
    let val d = Pivot.distance p in
      List.filter (fn (p, _) => d p < rq) [(pa, a), (pb, b)]
    end
    | range p rq (In ((pa, a), (pb, b), r, n1, n2, n3, n4)) =
    let
      val d = Pivot.distance p
      val ps = List.filter (fn (p, _) => d p < rq) [(pa, a), (pb, b)]
      val is = List.filter (intersect p rq) [n1, n2, n3, n4]
      val rs = List.map (range p rq) is
    in
      ps @ List.concat rs
    end
    | range p rq (Ex ((pa, a), (pb, b), r, l1, l2, l3, l4)) =
    let
      val d = Pivot.distance p
      val ls = (pa, a) :: (pa, b) :: List.concat (List.map list_leaf [l1, l2, l3, l4])
    in
      List.filter (fn (p, _) => d p < rq) ls
    end

end

structure Mm2dtree = Mmtree(Manhattan2D)
