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

datatype 'a mmnode = Lf
                   | Br of 'a * 'a * real * 'a mmnode * 'a mmnode * 'a mmnode * 'a mmnode

functor Mmtree (structure P : METRIC) :> MMTREE where type Pivot.t=P.t = struct
  structure Pivot : METRIC = P
  type 'a mmtree = (Pivot.t * 'a) mmnode

  fun intersect p rq Lf = false
    | intersect p rq (Br ((pa, a), (pb, b), r, n1, n2, n3, n4)) =
    let
      fun r1 () = Pivot.distance p pb < rq + r
                  andalso Pivot.distance p pa < rq + r
      fun r2 () = Pivot.distance p pb + rq >= r
                  andalso Pivot.distance p pa < rq + r
      fun r3 () = Pivot.distance p pb < rq + r
                  andalso Pivot.distance p pa + rq >= r
      fun r4 () = Pivot.distance p pb + rq >= r
                  andalso Pivot.distance p pa + rq >= r
    in
      r1 () orelse r2 () orelse r3 () orelse r4 ()
    end

  val empty = Lf

  fun insert (p, x) Lf = Br ((p, x), (p, x), 0.0, Lf, Lf, Lf, Lf)
    | insert (p, x) (Br ((pa, a), (pb, b), r, n1, n2, n3, n4)) =
    let
      val da = Pivot.distance p pa
      val db = Pivot.distance p pb
    in
      if da < r then
        if db < r then
          Br ((pa, a), (pb, b), r, insert (p, x) n1, n2, n3, n4)
        else
          Br ((pa, a), (pb, b), r, n1, insert (p, x) n2, n3, n4)
      else
        if db < r then
          Br ((pa, a), (pb, b), r, n1, n2, insert (p, x) n3, n4)
        else
          Br ((pa, a), (pb, b), r, n1, n2, n3, insert (p, x) n4)
    end

  fun range p rq Lf = []
    | range p rq (Br ((pa, a), (pb, b), r, n1, n2, n3, n4)) =
    let
      val d = Pivot.distance p
      val ps = List.filter (fn (p, _) => d p < rq) [(pa, a), (pb, b)]
      val is = List.filter (intersect p rq) [n1, n2, n3, n4]
      val rs = List.map (range p rq) is
    in
      ps @ List.concat rs
    end

end
