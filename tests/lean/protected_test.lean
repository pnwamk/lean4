namespace nat
  check induction_on      -- ERROR
  check rec_on            -- ERROR
  check nat.induction_on
  check less_than.rec_on         -- OK
  check nat.less_than.rec_on
  namespace le
    check rec_on          -- ERROR
    check less_than.rec_on
  end le
end nat
