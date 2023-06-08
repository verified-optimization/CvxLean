-- section QuasiConvex

-- def qp1 := 
--   optimization (x y : ℝ) 
--     minimize - (sqrt x) / y
--     subject to 
--       h1 : 0 < y
--       h2 : (exp x) ≤ y

-- reduction redq1/dcpq1 : qp1 := by
--   unfold qp1
--   -- convexify
--   exact done

-- end QuasiConvex