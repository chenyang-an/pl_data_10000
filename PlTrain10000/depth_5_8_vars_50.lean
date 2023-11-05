variable (p4 p6 p3 p2 p5 : Prop)
theorem file50_41 : ((((((p3 ∧ p6) ∨ (p2 ∨ p5)) → False) ∧ (((p6 ∨ p6) ∧ (False ∨ p5)) ∧ ((p6 → p4) ∧ (False ∧ p6)))) ∧ ((((p3 ∨ p2) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case inl assump_16 =>
              apply False.elim assump_16
            case inr assump_17 =>
              cases assump_9
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26
          case inr assump_13 =>
            cases assump_11
            case inl assump_32 =>
              apply False.elim assump_32
            case inr assump_33 =>
              cases assump_9
              case intro assump_38 assump_39 =>
                cases assump_39
                case intro assump_42 assump_43 =>
                  apply False.elim assump_42


variable (p6 p5 p4 p2 p1 p0 : Prop)
theorem file50_1276 : ((((((p0 → False) ∧ (p5 ∧ p2)) → ((p2 → p5) → (p1 → True))) ∨ (((p4 → p6) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p0 → False) ∧ (p5 ∧ p2)) → ((p2 → p5) → (p1 → True))) ∨ (((p4 → p6) → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p2 p5 p3 p4 p7 p0 p6 p1 : Prop)
theorem file50_1752 : (((((p4 ∨ p0) → (True → False)) ∨ ((True → p3) → (p0 ∧ p5))) ∧ (((p2 → p5) → (p3 → False)) → ((p1 ∧ p7) ∨ (p0 ∨ p7)))) → ((((p6 ∨ False) ∧ (p0 → False)) ∧ ((True ∧ p5) → (p1 → False))) ∨ (((p6 → False) → False) → ((p3 ∧ p1) → (True ∧ True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inr
      intro assump_10
      intro assump_11
      apply And.intro
      apply True.intro
      apply True.intro
    case inr assump_5 =>
      apply Or.inr
      intro assump_16
      intro assump_17
      apply And.intro
      apply True.intro
      apply True.intro


variable (p1 p2 p6 p5 p3 p7 p4 : Prop)
theorem file50_2464 : (((((False ∧ p2) → False) → False) → False) ∨ ((((p5 ∧ False) → False) ∧ ((p5 → False) → (False ∨ p3))) ∨ (((p6 → True) ∧ (p1 ∨ True)) ∨ ((p4 ∨ p7) ∧ (False ∧ True))))) := by
  apply Or.inl
  intro assump_12
  have assump_24 : ((False ∧ p2) → False) := by
    intro assump_16
    cases assump_16
    case intro assump_17 assump_18 =>
      apply False.elim assump_17
  let assump_15 := assump_12 assump_24
  apply False.elim assump_15


variable (p2 p5 p3 p1 : Prop)
theorem file50_2953 : (((((p1 → True) → (p3 → False)) → ((True ∧ False) → (p5 → False))) ∧ (((p1 → p1) ∧ (p5 ∧ p2)) ∧ ((False ∨ p2) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_24 : (False ∨ p2) := by
            apply Or.inr
            exact assump_13
          let assump_20 := assump_7 assump_24
          apply False.elim assump_20


variable (p2 p0 p4 p7 p1 : Prop)
theorem file50_3575 : (((((False ∨ p7) ∨ (p4 ∧ True)) → ((False → p0) ∧ (p0 → False))) → (((True → p1) → (False → p2)) ∨ ((True → p0) → (p1 ∧ True)))) ∨ ((((p0 → False) ∨ (False ∧ True)) ∧ ((p1 ∧ p1) → False)) → False)) := by
  apply Or.inl
  intro assump_30
  apply Or.inl
  intro assump_33
  intro assump_34
  apply False.elim assump_34


variable (p7 p1 p0 p5 p4 p2 p6 : Prop)
theorem file50_3955 : (((((True → p7) → (p2 ∧ p6)) → False) → (((p7 ∧ False) → (p0 ∨ p5)) ∨ ((True ∨ p7) ∧ (p5 ∨ p4)))) ∨ ((((p7 ∧ p6) ∨ (p6 → p1)) → ((p6 ∧ True) → False)) ∨ (((True → False) → (p0 ∧ p2)) ∨ ((p1 → False) ∧ (True → p2))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p1 p7 p2 p5 p0 p3 p6 : Prop)
theorem file50_4386 : ((((((p0 ∧ p6) → (True ∨ p2)) → ((p3 → p6) ∨ (p7 → False))) → (((p7 ∨ p1) → False) → ((p5 ∧ p0) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p0 ∧ p6) → (True ∨ p2)) → ((p3 → p6) ∨ (p7 → False))) → (((p7 ∨ p1) → False) → ((p5 ∧ p0) ∨ (False → False)))) := by
    intro assump_5
    intro assump_6
    apply Or.inr
    intro assump_11
    apply False.elim assump_11
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p1 p4 p2 p7 p5 p0 p3 : Prop)
theorem file50_4921 : (((((p5 ∨ p7) ∧ (p4 ∧ p7)) → ((False → p0) ∨ (p0 ∨ p5))) ∨ (((p6 ∧ p1) → False) → False)) ∨ ((((p6 → p2) → False) → ((p6 ∧ p2) ∧ (p3 → False))) ∨ (((p6 ∨ p1) → False) → ((p7 → p0) → (p1 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
    case inr assump_5 =>
      cases assump_3
      case intro assump_19 assump_20 =>
        apply Or.inl
        intro assump_25
        apply False.elim assump_25


variable (p3 p2 p0 p7 p5 : Prop)
theorem file50_5630 : ((((((p5 ∧ p0) → (p5 ∨ p7)) → False) → (((p5 → p3) ∨ (p0 → False)) ∧ ((p7 → False) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_43 : ((((p5 ∧ p0) → (p5 ∨ p7)) → False) → (((p5 → p3) ∨ (p0 → False)) ∧ ((p7 → False) ∨ (p2 → False)))) := by
    intro assump_5
    apply And.intro
    apply Or.inl
    intro assump_8
    have assump_44 : ((p5 ∧ p0) → (p5 ∨ p7)) := by
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply Or.inl
        exact assump_14
    let assump_12 := assump_5 assump_44
    apply False.elim assump_12
    apply Or.inl
    intro assump_25
    have assump_45 : ((p5 ∧ p0) → (p5 ∨ p7)) := by
      intro assump_30
      cases assump_30
      case intro assump_31 assump_32 =>
        apply Or.inl
        exact assump_31
    let assump_29 := assump_5 assump_45
    apply False.elim assump_29
  let assump_4 := assump_1 assump_43
  apply False.elim assump_4


variable (p7 p4 p2 p0 p5 : Prop)
theorem file50_6632 : ((((((p0 → False) ∧ (p0 ∧ p5)) → ((True → False) → False)) ∧ (((p7 → False) ∧ (False → False)) → ((p4 ∨ p7) → (False → p2)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((p0 → False) ∧ (p0 ∧ p5)) → ((True → False) → False)) ∧ (((p7 → False) ∧ (False → False)) → ((p4 ∨ p7) → (False → p2)))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        have assump_34 : p0 := by
          exact assump_13
        let assump_21 := assump_9 assump_34
        apply False.elim assump_21
    intro assump_25
    intro assump_26
    intro assump_27
    apply False.elim assump_27
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p6 : Prop)
theorem file50_7464 : ((((((p6 ∧ p6) → (True ∧ p6)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p6 ∧ p6) → (True ∧ p6)) → False) → False) := by
    intro assump_5
    have assump_23 : ((p6 ∧ p6) → (True ∧ p6)) := by
      intro assump_9
      apply And.intro
      apply True.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        exact assump_11
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p1 p0 p7 p5 p3 : Prop)
theorem file50_8041 : ((((((p1 → p1) → False) → False) ∨ (((p7 ∨ p2) → (p2 → p2)) ∨ ((p5 ∧ p3) ∨ (False ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p1 → p1) → False) → False) ∨ (((p7 ∨ p2) → (p2 → p2)) ∨ ((p5 ∧ p3) ∨ (False ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (p1 → p1) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p1 p6 p5 p2 p0 p4 p7 : Prop)
theorem file50_8599 : (((((p5 ∧ p7) → False) ∧ ((p2 ∨ False) → (p2 → False))) ∨ (((False ∨ p1) → (p6 ∨ p0)) → False)) → ((((True → False) ∧ (False ∧ p4)) ∧ ((p4 ∨ False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case intro assump_9 assump_10 =>
        apply False.elim assump_9


variable (p1 p5 p2 p7 p6 p3 p0 : Prop)
theorem file50_9070 : (((((p2 ∨ p0) → False) ∧ ((p7 → False) → False)) ∧ (((p1 ∨ p1) ∨ (True ∧ True)) → False)) → ((((p5 → False) ∧ (p1 → p2)) → ((True → False) ∧ (p5 ∨ p5))) ∨ (((p6 ∧ p7) → (p1 → p6)) ∨ ((True ∧ p2) → (p7 ∨ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_12
      apply And.intro
      intro assump_13
      cases assump_12
      case intro assump_16 assump_17 =>
        have assump_40 : ((p1 ∨ p1) ∨ (True ∧ True)) := by
          apply Or.inr
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_24 := assump_3 assump_40
        apply False.elim assump_24
      cases assump_12
      case intro assump_28 assump_29 =>
        have assump_41 : ((p1 ∨ p1) ∨ (True ∧ True)) := by
          apply Or.inr
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_36 := assump_3 assump_41
        apply False.elim assump_36


variable (p7 p5 p3 p4 p1 p2 : Prop)
theorem file50_10161 : (((((p4 → p3) → (p7 ∧ p2)) → ((p1 → False) ∨ (False → False))) → False) → ((((p5 ∨ p4) ∨ (p2 → p5)) → False) → (((p3 → False) ∧ (True ∨ False)) → ((False ∧ p7) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p3 p5 p2 p6 : Prop)
theorem file50_10542 : ((((((p2 → p5) ∧ (p6 → False)) → ((p3 → True) ∨ (p6 ∧ p2))) → (((True → False) → False) ∨ ((p2 ∧ p6) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p2 → p5) ∧ (p6 → False)) → ((p3 → True) ∨ (p6 ∧ p2))) → (((True → False) → False) ∨ ((p2 ∧ p6) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p6 p3 p0 p2 p4 : Prop)
theorem file50_11136 : (((((p4 → False) → False) → ((p3 ∨ p6) ∧ (p2 ∨ p4))) ∧ (((p7 ∨ p6) → (False → p0)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : ((p7 ∨ p6) → (False → p0)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p7 p3 p0 p1 p2 : Prop)
theorem file50_11568 : ((((((p7 ∧ p1) → False) ∧ ((p0 ∨ True) → False)) → (((p3 ∨ p2) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p7 ∧ p1) → False) ∧ ((p0 ∨ True) → False)) → (((p3 ∨ p2) → False) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      have assump_23 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_15 := assump_10 assump_23
      apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p7 p6 p0 p2 p1 : Prop)
theorem file50_12178 : (((((False ∧ p0) ∧ (True → p4)) → ((p1 → False) → False)) ∧ (((p6 ∨ p0) → False) ∧ ((p4 → p2) ∧ (p0 ∨ p4)))) → ((((p6 → False) ∨ (p1 ∨ p4)) → ((False ∧ p7) → False)) ∨ (((p6 → p0) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          intro assump_19
          cases assump_19
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
        case inr assump_15 =>
          apply Or.inl
          intro assump_26
          intro assump_27
          cases assump_27
          case intro assump_28 assump_29 =>
            apply False.elim assump_28


variable (p0 p4 p3 p5 p6 p1 p2 : Prop)
theorem file50_13083 : ((((((False ∧ p0) → False) ∨ ((p5 ∧ p4) → (False ∧ p3))) ∨ (((p2 ∧ p6) ∨ (p4 ∧ p1)) ∧ ((p6 → p6) ∧ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p0) → False) ∨ ((p5 ∧ p4) → (False ∧ p3))) ∨ (((p2 ∧ p6) ∨ (p4 ∧ p1)) ∧ ((p6 → p6) ∧ (True → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p2 p4 p1 p5 p0 p7 p3 : Prop)
theorem file50_13652 : (((((p6 ∧ p5) ∧ (p3 → p0)) → ((p0 ∨ False) → False)) ∨ (((p4 ∨ p5) ∨ (p7 ∧ p2)) → ((p5 → False) ∧ (p1 ∧ p6)))) → ((((p3 ∧ False) ∧ (p6 → p5)) ∧ ((False ∧ p7) → (p3 ∨ p1))) → (((True ∧ True) ∧ (False → p5)) ∧ ((False → p7) → (p1 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  apply True.intro
  apply True.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  apply And.intro
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        apply False.elim assump_14
  cases assump_2
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        apply False.elim assump_26


variable (p3 p7 p6 p5 p4 p1 p2 p0 : Prop)
theorem file50_14582 : (((((p4 → False) ∧ (p7 → False)) ∧ ((p4 → False) → (p3 ∨ p1))) ∧ (((p4 ∨ p5) → (p7 → False)) → ((p3 → p5) ∨ (p2 ∧ p0)))) → ((((False ∨ True) → False) → ((p0 ∨ p0) → False)) ∨ (((p6 ∧ p1) → (p5 → p6)) ∧ ((False ∨ p1) ∧ (True → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        cases assump_17
        case inl assump_18 =>
          have assump_36 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_24 := assump_16 assump_36
          apply False.elim assump_24
        case inr assump_19 =>
          have assump_37 : (False ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_32 := assump_16 assump_37
          apply False.elim assump_32


variable (p0 p2 p6 p3 p5 : Prop)
theorem file50_15589 : (((((p5 → False) → False) ∧ ((p5 → False) ∨ (p6 → False))) ∧ (((p0 ∨ p5) → False) ∧ ((p2 ∨ True) ∨ (p5 ∨ p0)))) → ((((p0 → p2) → False) ∨ ((p0 → False) ∨ (True ∨ p6))) ∨ (((p6 ∨ p3) → False) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case inl assump_16 =>
            cases assump_16
            case inl assump_18 =>
              apply Or.inl
              apply Or.inl
              intro assump_22
              have assump_168 : (p5 → False) := by
                intro assump_30
                have assump_169 : (p0 ∨ p5) := by
                  apply Or.inr
                  exact assump_30
                let assump_36 := assump_12 assump_169
                apply False.elim assump_36
              let assump_29 := assump_4 assump_168
              apply False.elim assump_29
            case inr assump_19 =>
              apply Or.inl
              apply Or.inl
              intro assump_45
              have assump_170 : (p5 → False) := by
                intro assump_52
                have assump_171 : (p0 ∨ p5) := by
                  apply Or.inr
                  exact assump_52
                let assump_57 := assump_12 assump_171
                apply False.elim assump_57
              let assump_51 := assump_4 assump_170
              apply False.elim assump_51
          case inr assump_17 =>
            cases assump_17
            case inl assump_64 =>
              apply Or.inl
              apply Or.inl
              intro assump_68
              have assump_172 : (p0 ∨ p5) := by
                apply Or.inr
                exact assump_64
              let assump_73 := assump_12 assump_172
              apply False.elim assump_73
            case inr assump_65 =>
              apply Or.inl
              apply Or.inl
              intro assump_79
              have assump_173 : (p0 ∨ p5) := by
                apply Or.inl
                exact assump_65
              let assump_85 := assump_12 assump_173
              apply False.elim assump_85
      case inr assump_9 =>
        cases assump_3
        case intro assump_91 assump_92 =>
          cases assump_92
          case inl assump_95 =>
            cases assump_95
            case inl assump_97 =>
              apply Or.inl
              apply Or.inl
              intro assump_101
              have assump_174 : (p5 → False) := by
                intro assump_109
                have assump_175 : (p0 ∨ p5) := by
                  apply Or.inr
                  exact assump_109
                let assump_115 := assump_91 assump_175
                apply False.elim assump_115
              let assump_108 := assump_4 assump_174
              apply False.elim assump_108
            case inr assump_98 =>
              apply Or.inl
              apply Or.inl
              intro assump_124
              have assump_176 : (p5 → False) := by
                intro assump_131
                have assump_177 : (p0 ∨ p5) := by
                  apply Or.inr
                  exact assump_131
                let assump_136 := assump_91 assump_177
                apply False.elim assump_136
              let assump_130 := assump_4 assump_176
              apply False.elim assump_130
          case inr assump_96 =>
            cases assump_96
            case inl assump_143 =>
              apply Or.inl
              apply Or.inl
              intro assump_147
              have assump_178 : (p0 ∨ p5) := by
                apply Or.inr
                exact assump_143
              let assump_152 := assump_91 assump_178
              apply False.elim assump_152
            case inr assump_144 =>
              apply Or.inl
              apply Or.inl
              intro assump_158
              have assump_179 : (p0 ∨ p5) := by
                apply Or.inl
                exact assump_144
              let assump_164 := assump_91 assump_179
              apply False.elim assump_164


variable (p6 p7 p3 p1 : Prop)
theorem file50_19795 : ((((((p1 ∨ p6) → False) ∧ ((p6 → True) → False)) → (((p6 ∨ p7) ∧ (p1 → False)) → ((False ∧ p3) ∨ (True ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((p1 ∨ p6) → False) ∧ ((p6 → True) → False)) → (((p6 ∨ p7) ∧ (p1 → False)) → ((False ∧ p3) ∨ (True ∧ p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_5
        case intro assump_15 assump_16 =>
          have assump_45 : (p6 → True) := by
            intro assump_22
            apply True.intro
          let assump_21 := assump_16 assump_45
          apply False.elim assump_21
      case inr assump_10 =>
        cases assump_5
        case intro assump_30 assump_31 =>
          have assump_46 : (p6 → True) := by
            intro assump_37
            apply True.intro
          let assump_36 := assump_31 assump_46
          apply False.elim assump_36
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p2 p6 p3 p1 p4 p5 p0 : Prop)
theorem file50_20882 : (((((p6 ∧ p1) ∧ (p0 → p6)) → ((p1 → False) → False)) ∨ (((p5 ∧ p2) ∧ (p2 ∨ p1)) → ((p0 → False) ∨ (p3 ∧ p3)))) ∨ ((((p3 ∨ p2) → (p6 ∧ p3)) ∧ ((p5 ∨ p2) ∨ (p3 → p2))) ∧ (((p1 → p0) → (p4 ∧ p1)) ∧ ((True ∧ True) ∧ (p0 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      have assump_22 : p1 := by
        exact assump_8
      let assump_18 := assump_2 assump_22
      apply False.elim assump_18


variable (p6 p2 p3 p4 p7 p5 p1 : Prop)
theorem file50_21480 : (((((p4 → True) → False) → ((p1 → False) ∨ (False → False))) ∨ (((p2 ∨ p2) → (False → True)) → ((p6 → p1) → False))) ∨ ((((p1 → True) → False) → False) ∧ (((p5 ∧ p2) ∨ (p3 → False)) ∨ ((p1 → False) → (p5 ∧ p7))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_13 : (p4 → True) := by
    intro assump_9
    apply True.intro
  let assump_8 := assump_1 assump_13
  apply False.elim assump_8


variable (p0 p5 p6 p4 p2 p7 p1 : Prop)
theorem file50_21984 : (((((p5 ∨ p4) ∨ (p0 ∨ True)) ∨ ((p5 ∧ p6) → False)) → (((p4 ∨ False) ∧ (p2 ∨ p0)) → ((True ∧ p1) → (p4 ∨ p0)))) ∨ ((((p6 → False) → False) → False) ∧ (((p1 ∨ p4) ∨ (p7 → p5)) ∨ ((p2 → False) → False)))) := by
  apply Or.inl
  intro assump_15
  intro assump_16
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_16
    case intro assump_24 assump_25 =>
      cases assump_24
      case inl assump_26 =>
        cases assump_25
        case inl assump_30 =>
          cases assump_15
          case inl assump_34 =>
            cases assump_34
            case inl assump_36 =>
              cases assump_36
              case inl assump_38 =>
                apply Or.inl
                exact assump_26
              case inr assump_39 =>
                apply Or.inl
                exact assump_39
            case inr assump_37 =>
              cases assump_37
              case inl assump_44 =>
                apply Or.inl
                exact assump_26
              case inr assump_45 =>
                apply Or.inl
                exact assump_26
          case inr assump_35 =>
            apply Or.inl
            exact assump_26
        case inr assump_31 =>
          cases assump_15
          case inl assump_54 =>
            cases assump_54
            case inl assump_56 =>
              cases assump_56
              case inl assump_58 =>
                apply Or.inl
                exact assump_26
              case inr assump_59 =>
                apply Or.inl
                exact assump_59
            case inr assump_57 =>
              cases assump_57
              case inl assump_64 =>
                apply Or.inl
                exact assump_26
              case inr assump_65 =>
                apply Or.inl
                exact assump_26
          case inr assump_55 =>
            apply Or.inl
            exact assump_26
      case inr assump_27 =>
        apply False.elim assump_27


variable (p1 p2 p7 p4 : Prop)
theorem file50_23999 : (((((False → False) → False) → False) ∨ (((p1 → False) → (p2 → False)) ∧ ((False → False) → (False → p1)))) ∨ ((((p2 → False) → False) → False) → (((False ∨ p4) → False) ∨ ((p1 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_5
  have assump_15 : (False → False) := by
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_5 assump_15
  apply False.elim assump_8


variable (p1 p7 p2 p6 p5 p0 p4 : Prop)
theorem file50_24465 : (((((p4 → p2) → (p1 → False)) ∧ ((False ∨ p2) ∧ (p7 ∧ p1))) → (((p6 ∨ p0) → False) → False)) ∨ ((((p6 ∧ p7) ∧ (p4 ∧ p5)) ∧ ((True → p0) → False)) → (((p0 ∨ p1) ∧ (p6 ∨ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply False.elim assump_11
      case inr assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          have assump_34 : (p4 → p2) := by
            intro assump_27
            exact assump_12
          let assump_26 := assump_5 assump_34
          have assump_35 : p1 := by
            exact assump_18
          let assump_30 := assump_26 assump_35
          apply False.elim assump_30


variable (p6 p3 p1 p5 p2 p0 p4 : Prop)
theorem file50_25345 : (((((False → False) ∨ (True ∧ p4)) → False) → (((p2 ∨ False) → False) ∨ ((p3 → p0) → (p6 → False)))) ∨ ((((p4 → False) ∨ (p2 ∧ p2)) → ((p1 → False) → (p5 → False))) → False)) := by
  apply Or.inl
  intro assump_10
  apply Or.inl
  intro assump_13
  cases assump_13
  case inl assump_14 =>
    have assump_28 : ((False → False) ∨ (True ∧ p4)) := by
      apply Or.inl
      intro assump_20
      apply False.elim assump_20
    let assump_19 := assump_10 assump_28
    apply False.elim assump_19
  case inr assump_15 =>
    apply False.elim assump_15


variable (p2 p0 p5 : Prop)
theorem file50_25945 : (((((p2 ∧ p0) ∨ (p0 ∧ p0)) ∨ ((p0 ∧ p2) → (p5 → p5))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p2 ∧ p0) ∨ (p0 ∧ p0)) ∨ ((p0 ∧ p2) → (p5 → p5))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      exact assump_6
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p5 p2 p7 p1 p6 p3 : Prop)
theorem file50_26377 : (((((p7 ∧ p5) ∧ (p5 ∧ p6)) → False) ∧ (((p2 ∧ False) ∨ (p3 → False)) ∧ ((p6 ∧ False) ∧ (p1 ∧ p4)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_9 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_21


variable (p0 p6 p4 p5 p3 : Prop)
theorem file50_27023 : (((((p3 ∨ p5) ∨ (False ∧ p0)) → ((True → p0) → (False → p4))) → False) → ((((True → True) → False) → ((p5 → p5) ∧ (False → p6))) → False)) := by
  intro assump_11
  intro assump_12
  have assump_26 : (((p3 ∨ p5) ∨ (False ∧ p0)) → ((True → p0) → (False → p4))) := by
    intro assump_18
    intro assump_19
    intro assump_20
    apply False.elim assump_20
  let assump_17 := assump_11 assump_26
  apply False.elim assump_17


variable (p5 p0 p2 p1 p7 p6 p4 : Prop)
theorem file50_27511 : (((((p4 ∨ p2) ∧ (p6 ∧ True)) → ((False ∨ True) ∨ (p0 → False))) → False) → ((((False ∧ p5) → (p1 → p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_32 : (((p4 ∨ p2) ∧ (p6 ∧ True)) → ((False ∨ True) ∨ (p0 → False))) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_12 =>
        cases assump_10
        case intro assump_23 assump_24 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_7 := assump_1 assump_32
  apply False.elim assump_7


variable (p0 p1 p2 p4 p6 p3 : Prop)
theorem file50_28316 : ((((((p0 ∨ True) → False) ∧ ((False ∨ p6) ∧ (False ∧ p2))) ∧ (((p0 ∧ p3) ∧ (False ∨ p1)) → False)) ∧ ((((p2 ∧ p2) ∨ (p4 → False)) ∧ ((p4 → p3) ∧ (p1 ∧ p2))) ∨ (((p3 → p6) → False) ∨ ((p4 → False) ∨ (p6 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_18


variable (p6 p4 p0 p1 p5 p7 : Prop)
theorem file50_29097 : (((((True → False) → (p6 ∧ p5)) ∨ ((False ∧ p5) → False)) → False) → ((((p5 ∨ p4) → False) ∧ ((False ∧ p7) ∧ (p0 ∧ p6))) ∨ (((False → p1) → False) → False))) := by
  intro assump_1
  apply Or.inr
  intro assump_43
  have assump_53 : (False → p1) := by
    intro assump_47
    apply False.elim assump_47
  let assump_46 := assump_43 assump_53
  apply False.elim assump_46


variable (p1 p0 p4 p6 p7 p3 p2 : Prop)
theorem file50_29531 : (((((p2 ∧ p4) → False) ∧ ((p2 ∨ p1) ∧ (p7 → False))) ∧ (((p3 ∨ p0) ∧ (p6 → False)) ∧ ((p0 ∧ p7) ∨ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_17
                case inl assump_26 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    have assump_136 : p7 := by
                      exact assump_29
                    let assump_38 := assump_9 assump_136
                    apply False.elim assump_38
                case inr assump_27 =>
                  have assump_137 : True := by
                    apply True.intro
                  let assump_44 := assump_27 assump_137
                  apply False.elim assump_44
              case inr assump_21 =>
                cases assump_17
                case inl assump_52 =>
                  cases assump_52
                  case intro assump_54 assump_55 =>
                    have assump_138 : p7 := by
                      exact assump_55
                    let assump_64 := assump_9 assump_138
                    apply False.elim assump_64
                case inr assump_53 =>
                  have assump_139 : True := by
                    apply True.intro
                  let assump_70 := assump_53 assump_139
                  apply False.elim assump_70
        case inr assump_11 =>
          cases assump_3
          case intro assump_78 assump_79 =>
            cases assump_78
            case intro assump_80 assump_81 =>
              cases assump_80
              case inl assump_82 =>
                cases assump_79
                case inl assump_88 =>
                  cases assump_88
                  case intro assump_90 assump_91 =>
                    have assump_140 : p7 := by
                      exact assump_91
                    let assump_100 := assump_9 assump_140
                    apply False.elim assump_100
                case inr assump_89 =>
                  have assump_141 : True := by
                    apply True.intro
                  let assump_106 := assump_89 assump_141
                  apply False.elim assump_106
              case inr assump_83 =>
                cases assump_79
                case inl assump_114 =>
                  cases assump_114
                  case intro assump_116 assump_117 =>
                    have assump_142 : p7 := by
                      exact assump_117
                    let assump_126 := assump_9 assump_142
                    apply False.elim assump_126
                case inr assump_115 =>
                  have assump_143 : True := by
                    apply True.intro
                  let assump_132 := assump_115 assump_143
                  apply False.elim assump_132


variable (p1 p4 p3 p2 p5 : Prop)
theorem file50_32761 : ((((((p4 → p2) ∧ (True → p5)) → ((p4 ∨ p3) → False)) → (((p1 → p1) ∨ (True → True)) ∨ ((p1 → p4) ∧ (p1 → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p4 → p2) ∧ (True → p5)) → ((p4 ∨ p3) → False)) → (((p1 → p1) ∨ (True → True)) ∨ ((p1 → p4) ∧ (p1 → False)))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p3 p4 p7 p0 p5 : Prop)
theorem file50_33271 : (((((False ∧ p4) → (True → False)) ∨ ((p1 ∧ False) ∨ (p4 ∨ False))) ∨ (((p7 → p3) → (p4 → p7)) ∧ ((p0 ∨ p5) → False))) → ((((p3 ∧ p7) ∧ (True → False)) → ((p4 → p4) ∧ (p3 ∧ True))) ∨ (((p4 ∨ p7) → False) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      intro assump_8
      apply And.intro
      intro assump_9
      cases assump_8
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          exact assump_9
      apply And.intro
      cases assump_8
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          exact assump_24
      apply True.intro
    case inr assump_5 =>
      cases assump_5
      case inl assump_32 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          apply False.elim assump_35
      case inr assump_33 =>
        cases assump_33
        case inl assump_40 =>
          apply Or.inl
          intro assump_44
          apply And.intro
          intro assump_45
          cases assump_44
          case intro assump_48 assump_49 =>
            cases assump_48
            case intro assump_50 assump_51 =>
              exact assump_45
          apply And.intro
          cases assump_44
          case intro assump_58 assump_59 =>
            cases assump_58
            case intro assump_60 assump_61 =>
              exact assump_60
          apply True.intro
        case inr assump_41 =>
          apply False.elim assump_41
  case inr assump_3 =>
    cases assump_3
    case intro assump_70 assump_71 =>
      apply Or.inl
      intro assump_76
      apply And.intro
      intro assump_77
      cases assump_76
      case intro assump_80 assump_81 =>
        cases assump_80
        case intro assump_82 assump_83 =>
          exact assump_77
      apply And.intro
      cases assump_76
      case intro assump_90 assump_91 =>
        cases assump_90
        case intro assump_92 assump_93 =>
          exact assump_92
      apply True.intro


variable (p3 p6 p5 p2 p7 p0 p1 : Prop)
theorem file50_35435 : ((((((p2 → p3) → False) ∨ ((p2 ∨ p0) → False)) → (((p3 → False) → (p6 → False)) ∧ ((p2 ∧ p0) ∧ (p7 ∧ True)))) ∧ ((((p3 ∨ p2) → (p1 ∨ p5)) → ((p3 ∨ True) ∧ (p3 → True))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_20 : (((p3 ∨ p2) → (p1 ∨ p5)) → ((p3 ∨ True) ∧ (p3 → True))) := by
      intro assump_13
      apply And.intro
      apply Or.inr
      apply True.intro
      intro assump_16
      apply True.intro
    let assump_12 := assump_7 assump_20
    apply False.elim assump_12


variable (p3 p7 p6 p0 p1 p4 : Prop)
theorem file50_36042 : (((((p4 ∨ True) ∨ (p6 → False)) ∧ ((p0 ∧ p3) ∧ (False → False))) → (((p1 → p1) → False) → ((p6 → False) → False))) ∧ ((((p6 ∧ False) ∧ (p7 ∧ p0)) ∨ ((p4 → p4) → False)) → False)) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            have assump_102 : (p1 → p1) := by
              intro assump_31
              exact assump_31
            let assump_30 := assump_2 assump_102
            apply False.elim assump_30
      case inr assump_13 =>
        cases assump_9
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            have assump_103 : (p1 → p1) := by
              intro assump_53
              exact assump_53
            let assump_52 := assump_2 assump_103
            apply False.elim assump_52
    case inr assump_11 =>
      cases assump_9
      case intro assump_61 assump_62 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          have assump_104 : (p1 → p1) := by
            intro assump_76
            exact assump_76
          let assump_75 := assump_2 assump_104
          apply False.elim assump_75
  intro assump_82
  cases assump_82
  case inl assump_83 =>
    cases assump_83
    case intro assump_85 assump_86 =>
      cases assump_85
      case intro assump_87 assump_88 =>
        apply False.elim assump_88
  case inr assump_84 =>
    have assump_105 : (p4 → p4) := by
      intro assump_96
      exact assump_96
    let assump_95 := assump_84 assump_105
    apply False.elim assump_95


variable (p0 p1 : Prop)
theorem file50_37907 : ((((((p1 ∧ True) ∨ (p1 → False)) → False) → (((p0 ∧ False) ∨ (True → False)) → False)) → False) → False) := by
  intro assump_12
  have assump_45 : ((((p1 ∧ True) ∨ (p1 → False)) → False) → (((p0 ∧ False) ∨ (True → False)) → False)) := by
    intro assump_16
    intro assump_17
    cases assump_17
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
    case inr assump_19 =>
      have assump_46 : ((p1 ∧ True) ∨ (p1 → False)) := by
        apply Or.inr
        intro assump_31
        have assump_47 : ((p1 ∧ True) ∨ (p1 → False)) := by
          apply Or.inl
          apply And.intro
          exact assump_31
          apply True.intro
        let assump_35 := assump_16 assump_47
        apply False.elim assump_35
      let assump_30 := assump_16 assump_46
      apply False.elim assump_30
  let assump_15 := assump_12 assump_45
  apply False.elim assump_15


variable (p3 p1 p2 p0 p5 p4 p6 : Prop)
theorem file50_38907 : ((((((p4 → False) → False) ∨ ((p2 → False) ∧ (p2 ∨ p4))) ∧ (((False ∧ p4) ∧ (True → True)) → ((p2 ∨ p6) ∨ (False → p1)))) ∧ ((((p6 ∨ p6) ∨ (p6 ∨ True)) → False) ∨ (((p5 → False) → (p5 → p5)) ∧ ((p0 ∨ p3) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_12 =>
          have assump_122 : ((p6 ∨ p6) ∨ (p6 ∨ True)) := by
            apply Or.inr
            apply Or.inr
            apply True.intro
          let assump_16 := assump_12 assump_122
          apply False.elim assump_16
        case inr assump_13 =>
          cases assump_13
          case intro assump_20 assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              cases assump_24
              case inl assump_26 =>
                have assump_123 : True := by
                  apply True.intro
                let assump_32 := assump_25 assump_123
                apply False.elim assump_32
              case inr assump_27 =>
                have assump_124 : True := by
                  apply True.intro
                let assump_40 := assump_25 assump_124
                apply False.elim assump_40
      case inr assump_7 =>
        cases assump_7
        case intro assump_44 assump_45 =>
          cases assump_45
          case inl assump_48 =>
            cases assump_3
            case inl assump_54 =>
              have assump_125 : ((p6 ∨ p6) ∨ (p6 ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_58 := assump_54 assump_125
              apply False.elim assump_58
            case inr assump_55 =>
              cases assump_55
              case intro assump_62 assump_63 =>
                cases assump_63
                case intro assump_66 assump_67 =>
                  cases assump_66
                  case inl assump_68 =>
                    have assump_126 : True := by
                      apply True.intro
                    let assump_74 := assump_67 assump_126
                    apply False.elim assump_74
                  case inr assump_69 =>
                    have assump_127 : True := by
                      apply True.intro
                    let assump_82 := assump_67 assump_127
                    apply False.elim assump_82
          case inr assump_49 =>
            cases assump_3
            case inl assump_90 =>
              have assump_128 : ((p6 ∨ p6) ∨ (p6 ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_94 := assump_90 assump_128
              apply False.elim assump_94
            case inr assump_91 =>
              cases assump_91
              case intro assump_98 assump_99 =>
                cases assump_99
                case intro assump_102 assump_103 =>
                  cases assump_102
                  case inl assump_104 =>
                    have assump_129 : True := by
                      apply True.intro
                    let assump_110 := assump_103 assump_129
                    apply False.elim assump_110
                  case inr assump_105 =>
                    have assump_130 : True := by
                      apply True.intro
                    let assump_118 := assump_103 assump_130
                    apply False.elim assump_118


variable (p7 p6 p2 p1 p3 p0 : Prop)
theorem file50_42484 : ((((((p6 ∨ p1) ∨ (p3 ∨ p7)) ∨ ((p2 ∧ p0) ∨ (True ∨ p0))) ∨ (((p0 → p2) ∧ (p3 → True)) ∧ ((p6 ∧ p2) → (False → False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p6 ∨ p1) ∨ (p3 ∨ p7)) ∨ ((p2 ∧ p0) ∨ (True ∨ p0))) ∨ (((p0 → p2) ∧ (p3 → True)) ∧ ((p6 ∧ p2) → (False → False)))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p7 p5 p2 : Prop)
theorem file50_42994 : (((((False → False) → False) → False) ∧ (((p5 → False) ∧ (p7 ∨ p2)) ∧ ((False → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_36 : (False → p1) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_7 assump_36
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_37 : (False → p1) := by
            intro assump_30
            apply False.elim assump_30
          let assump_29 := assump_7 assump_37
          apply False.elim assump_29


variable (p1 : Prop)
theorem file50_43806 : ((((((False ∧ p1) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ p1) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ p1) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p3 p5 p1 p4 p0 p7 : Prop)
theorem file50_44340 : (((((True → False) ∨ (True → False)) ∧ ((p7 ∧ p1) → (p0 ∧ p4))) → (((p1 → p7) ∨ (p7 → True)) → False)) ∨ ((((p0 ∧ False) ∧ (False → p1)) → False) → (((p3 → False) → False) ∧ ((p3 ∧ True) ∨ (p5 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        have assump_53 : True := by
          apply True.intro
        let assump_16 := assump_9 assump_53
        apply False.elim assump_16
      case inr assump_10 =>
        have assump_54 : True := by
          apply True.intro
        let assump_25 := assump_10 assump_54
        apply False.elim assump_25
  case inr assump_4 =>
    cases assump_1
    case intro assump_31 assump_32 =>
      cases assump_31
      case inl assump_33 =>
        have assump_55 : True := by
          apply True.intro
        let assump_40 := assump_33 assump_55
        apply False.elim assump_40
      case inr assump_34 =>
        have assump_56 : True := by
          apply True.intro
        let assump_49 := assump_34 assump_56
        apply False.elim assump_49


variable (p7 p2 p5 p6 p1 p3 p0 : Prop)
theorem file50_45561 : (((((p6 ∧ True) ∧ (True → False)) → False) ∨ (((p3 → False) ∨ (p2 ∨ p5)) ∧ ((p2 ∧ p5) ∧ (p6 → False)))) ∨ ((((p1 ∨ p0) → False) ∧ ((p7 → False) → False)) ∧ (((True ∨ p1) ∧ (False ∧ p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_16 : True := by
        apply True.intro
      let assump_12 := assump_3 assump_16
      apply False.elim assump_12


variable (p7 p3 p4 p6 p0 p1 p5 p2 : Prop)
theorem file50_46117 : (((((False → p0) ∨ (p0 ∨ False)) ∧ ((p2 ∧ p5) ∧ (p2 → False))) → (((True → p4) ∨ (False ∨ False)) → ((p7 → False) → False))) ∨ ((((p1 → False) ∨ (p0 → p3)) → ((True → p6) → (p3 → p2))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            have assump_56 : p2 := by
              exact assump_18
            let assump_26 := assump_17 assump_56
            apply False.elim assump_26
      case inr assump_13 =>
        cases assump_13
        case inl assump_30 =>
          cases assump_11
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              have assump_57 : p2 := by
                exact assump_36
              let assump_44 := assump_35 assump_57
              apply False.elim assump_44
        case inr assump_31 =>
          apply False.elim assump_31
  case inr assump_7 =>
    cases assump_7
    case inl assump_50 =>
      apply False.elim assump_50
    case inr assump_51 =>
      apply False.elim assump_51


variable (p4 p3 p2 p5 p1 p0 p6 : Prop)
theorem file50_47503 : ((((((p6 → p5) → (p3 → p0)) ∧ ((p4 → p3) ∨ (p6 → p4))) → (((p2 ∨ True) ∨ (p6 → p1)) ∨ ((p3 → False) → False))) → False) → False) := by
  intro assump_9
  have assump_27 : ((((p6 → p5) → (p3 → p0)) ∧ ((p4 → p3) ∨ (p6 → p4))) → (((p2 ∨ True) ∨ (p6 → p1)) ∨ ((p3 → False) → False))) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_15
      case inl assump_18 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_19 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
  let assump_12 := assump_9 assump_27
  apply False.elim assump_12


variable (p5 p3 p2 p4 p6 p1 : Prop)
theorem file50_48248 : (((((True → False) → (p4 ∨ p5)) → ((p6 ∧ p4) ∨ (p1 ∧ p4))) ∧ (((p2 ∧ p3) ∧ (True → p3)) ∧ ((p1 ∧ p3) ∧ (p4 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_7
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              have assump_70 : ((True → False) → (p4 ∨ p5)) := by
                intro assump_36
                have assump_71 : True := by
                  apply True.intro
                let assump_39 := assump_36 assump_71
                apply False.elim assump_39
              let assump_35 := assump_2 assump_70
              cases assump_35
              case inl assump_44 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  have assump_72 : p4 := by
                    exact assump_47
                  let assump_54 := assump_19 assump_72
                  apply False.elim assump_54
              case inr assump_45 =>
                cases assump_45
                case intro assump_58 assump_59 =>
                  have assump_73 : p4 := by
                    exact assump_59
                  let assump_66 := assump_19 assump_73
                  apply False.elim assump_66


variable (p2 p4 p0 : Prop)
theorem file50_49772 : ((((((False → False) → False) ∨ ((False → False) → False)) → (((p2 ∨ p0) → False) ∨ ((True → False) ∧ (p4 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_61 : ((((False → False) → False) ∨ ((False → False) → False)) → (((p2 ∨ p0) → False) ∨ ((True → False) ∧ (p4 ∨ True)))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        have assump_62 : (False → False) := by
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_6 assump_62
        apply False.elim assump_16
      case inr assump_12 =>
        have assump_63 : (False → False) := by
          intro assump_27
          apply False.elim assump_27
        let assump_26 := assump_6 assump_63
        apply False.elim assump_26
    case inr assump_7 =>
      apply Or.inl
      intro assump_35
      cases assump_35
      case inl assump_36 =>
        have assump_64 : (False → False) := by
          intro assump_42
          apply False.elim assump_42
        let assump_41 := assump_7 assump_64
        apply False.elim assump_41
      case inr assump_37 =>
        have assump_65 : (False → False) := by
          intro assump_52
          apply False.elim assump_52
        let assump_51 := assump_7 assump_65
        apply False.elim assump_51
  let assump_4 := assump_1 assump_61
  apply False.elim assump_4


variable (p4 p5 p3 p2 p7 p1 p6 : Prop)
theorem file50_51280 : (((((p5 ∧ p7) → False) → ((p4 → True) ∨ (p6 → False))) ∨ (((p1 ∧ True) ∨ (p1 → False)) ∨ ((False → p4) → False))) ∨ ((((p3 ∨ p5) ∨ (p4 ∧ p3)) → ((p2 → p2) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  apply True.intro


variable (p2 p6 p4 p3 p5 p7 p0 p1 : Prop)
theorem file50_51625 : (((((p0 ∨ p3) ∨ (False ∧ True)) → False) → (((p3 ∧ p3) → (p4 → False)) ∨ ((p1 ∨ p4) → (p6 ∧ False)))) ∨ ((((p4 → p7) → False) ∨ ((p1 → False) → (p6 ∨ p0))) ∧ (((False ∧ p7) ∧ (p2 ∨ p5)) ∧ ((p1 ∧ p6) → False)))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    have assump_21 : ((p0 ∨ p3) ∨ (False ∧ True)) := by
      apply Or.inl
      apply Or.inr
      exact assump_9
    let assump_17 := assump_1 assump_21
    apply False.elim assump_17


variable (p3 p4 p0 p6 p7 p5 p2 : Prop)
theorem file50_52223 : ((((((p5 → False) → False) → False) ∧ (((True → p6) ∨ (False → p3)) ∨ ((p7 ∧ False) → False))) ∧ ((((p0 ∨ True) → False) → False) ∧ (((p4 ∨ False) → False) ∧ ((p2 → p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case intro assump_18 assump_19 =>
              have assump_69 : (p2 → p2) := by
                intro assump_25
                exact assump_25
              let assump_24 := assump_19 assump_69
              apply False.elim assump_24
        case inr assump_11 =>
          cases assump_3
          case intro assump_33 assump_34 =>
            cases assump_34
            case intro assump_37 assump_38 =>
              have assump_70 : (p2 → p2) := by
                intro assump_44
                exact assump_44
              let assump_43 := assump_38 assump_70
              apply False.elim assump_43
      case inr assump_9 =>
        cases assump_3
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            have assump_71 : (p2 → p2) := by
              intro assump_63
              exact assump_63
            let assump_62 := assump_57 assump_71
            apply False.elim assump_62


variable (p0 p2 p1 p5 p7 : Prop)
theorem file50_53777 : ((((((p7 ∧ True) → False) ∨ ((p0 ∧ p5) ∧ (p0 ∨ p2))) → False) ∧ ((((False ∨ p1) → False) ∨ ((p0 → False) ∧ (p5 → False))) ∧ (((True → False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_44 : ((True → False) → False) := by
          intro assump_15
          have assump_45 : True := by
            apply True.intro
          let assump_18 := assump_15 assump_45
          apply False.elim assump_18
        let assump_14 := assump_7 assump_44
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_25 assump_26 =>
          have assump_46 : ((True → False) → False) := by
            intro assump_34
            have assump_47 : True := by
              apply True.intro
            let assump_37 := assump_34 assump_47
            apply False.elim assump_37
          let assump_33 := assump_7 assump_46
          apply False.elim assump_33


variable (p6 p0 p1 p2 p5 p4 p7 : Prop)
theorem file50_54919 : ((((((p0 ∨ p1) ∧ (p2 → p5)) ∨ ((p7 ∧ p0) → False)) → (((True ∧ False) ∧ (p4 ∨ p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∨ p1) ∧ (p2 → p5)) ∨ ((p7 ∧ p0) → False)) → (((True ∧ False) ∧ (p4 ∨ p6)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p6 p1 p4 p2 : Prop)
theorem file50_55479 : ((((((False ∨ False) → (True ∨ p7)) → False) ∧ (((p1 → p4) ∧ (p7 ∧ False)) ∧ ((p1 → False) ∧ (p2 → False)))) ∧ ((((True → False) → (p4 ∧ p2)) → ((p6 ∧ p7) ∨ (p4 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            apply False.elim assump_15


variable (p2 p1 p3 p4 p5 : Prop)
theorem file50_56089 : (((((False → False) ∧ (True ∧ False)) ∨ ((p1 ∧ p2) ∧ (p4 ∧ False))) ∨ (((False → p1) ∨ (True ∧ p5)) → False)) → ((((p3 → False) ∧ (p1 ∧ p5)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_10
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
    case inr assump_8 =>
      cases assump_8
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_20
          case intro assump_27 assump_28 =>
            apply False.elim assump_28
  case inr assump_6 =>
    have assump_42 : ((False → p1) ∨ (True ∧ p5)) := by
      apply Or.inl
      intro assump_36
      apply False.elim assump_36
    let assump_35 := assump_6 assump_42
    apply False.elim assump_35


variable (p4 p7 p3 p6 p0 p5 p2 : Prop)
theorem file50_57084 : (((((False ∧ p0) → False) ∨ ((p0 → False) ∧ (True ∧ True))) ∨ (((p2 ∧ p3) ∧ (p7 ∨ p6)) → False)) ∧ ((((p0 ∨ p7) ∧ (p4 → False)) ∧ ((p3 → p5) → False)) ∨ (((p4 → p4) → False) → False))) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  apply Or.inr
  intro assump_6
  have assump_16 : (p4 → p4) := by
    intro assump_10
    exact assump_10
  let assump_9 := assump_6 assump_16
  apply False.elim assump_9


variable (p2 p0 p6 p4 : Prop)
theorem file50_57647 : ((((((True ∧ p2) ∧ (True ∨ p4)) → False) → (((True ∨ p2) ∨ (p2 → p0)) ∨ ((p2 → p0) ∨ (p6 ∨ p0)))) ∧ ((((False → p4) ∨ (p4 → p4)) → False) ∧ (((False ∧ False) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_21 : ((False ∧ False) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
      let assump_12 := assump_7 assump_21
      apply False.elim assump_12


variable (p0 p3 p2 p5 p7 p4 p1 : Prop)
theorem file50_58283 : (((((False → False) → False) → ((p7 ∨ p5) → False)) → False) → ((((p4 ∨ p7) ∨ (p3 → False)) → ((p5 → False) ∨ (p5 → False))) ∨ (((p2 ∨ p5) → False) ∨ ((p7 → False) ∧ (p0 → p1))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      have assump_120 : (((False → False) → False) → ((p7 ∨ p5) → False)) := by
        intro assump_17
        intro assump_18
        cases assump_18
        case inl assump_19 =>
          have assump_121 : (False → False) := by
            intro assump_26
            apply False.elim assump_26
          let assump_25 := assump_17 assump_121
          apply False.elim assump_25
        case inr assump_20 =>
          have assump_122 : (False → False) := by
            intro assump_37
            apply False.elim assump_37
          let assump_36 := assump_17 assump_122
          apply False.elim assump_36
      let assump_16 := assump_1 assump_120
      apply False.elim assump_16
    case inr assump_8 =>
      apply Or.inl
      intro assump_48
      have assump_123 : (((False → False) → False) → ((p7 ∨ p5) → False)) := by
        intro assump_54
        intro assump_55
        cases assump_55
        case inl assump_56 =>
          have assump_124 : (False → False) := by
            intro assump_63
            apply False.elim assump_63
          let assump_62 := assump_54 assump_124
          apply False.elim assump_62
        case inr assump_57 =>
          have assump_125 : (False → False) := by
            intro assump_74
            apply False.elim assump_74
          let assump_73 := assump_54 assump_125
          apply False.elim assump_73
      let assump_53 := assump_1 assump_123
      apply False.elim assump_53
  case inr assump_6 =>
    apply Or.inl
    intro assump_85
    have assump_126 : (((False → False) → False) → ((p7 ∨ p5) → False)) := by
      intro assump_91
      intro assump_92
      cases assump_92
      case inl assump_93 =>
        have assump_127 : (False → False) := by
          intro assump_100
          apply False.elim assump_100
        let assump_99 := assump_91 assump_127
        apply False.elim assump_99
      case inr assump_94 =>
        have assump_128 : (False → False) := by
          intro assump_111
          apply False.elim assump_111
        let assump_110 := assump_91 assump_128
        apply False.elim assump_110
    let assump_90 := assump_1 assump_126
    apply False.elim assump_90


variable (p0 p6 p7 p1 p2 : Prop)
theorem file50_60872 : (((((p6 ∧ p2) → False) → False) ∧ (((p0 → False) → (p7 → True)) → False)) → ((((p7 → False) ∨ (p1 ∧ p0)) → ((p6 → True) → False)) ∨ (((p1 ∨ p6) → False) → ((p6 ∧ False) → (True → False))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    intro assump_12
    intro assump_13
    cases assump_12
    case inl assump_16 =>
      have assump_43 : ((p0 → False) → (p7 → True)) := by
        intro assump_23
        intro assump_24
        apply True.intro
      let assump_22 := assump_7 assump_43
      apply False.elim assump_22
    case inr assump_17 =>
      cases assump_17
      case intro assump_28 assump_29 =>
        have assump_44 : ((p0 → False) → (p7 → True)) := by
          intro assump_38
          intro assump_39
          apply True.intro
        let assump_37 := assump_7 assump_44
        apply False.elim assump_37


variable (p4 p2 p5 p6 p3 p1 : Prop)
theorem file50_61811 : ((((((p2 ∧ p3) → (True → False)) ∧ ((p6 ∧ True) ∨ (p1 → False))) ∨ (((False ∨ p6) → False) ∨ ((p1 ∨ p5) ∧ (p6 ∨ p4)))) ∧ ((((True ∨ p3) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            have assump_135 : (((True ∨ p3) → False) → False) := by
              intro assump_21
              have assump_136 : (True ∨ p3) := by
                apply Or.inl
                apply True.intro
              let assump_24 := assump_21 assump_136
              apply False.elim assump_24
            let assump_20 := assump_3 assump_135
            apply False.elim assump_20
        case inr assump_11 =>
          have assump_137 : (((True ∨ p3) → False) → False) := by
            intro assump_36
            have assump_138 : (True ∨ p3) := by
              apply Or.inl
              apply True.intro
            let assump_39 := assump_36 assump_138
            apply False.elim assump_39
          let assump_35 := assump_3 assump_137
          apply False.elim assump_35
    case inr assump_5 =>
      cases assump_5
      case inl assump_46 =>
        have assump_139 : (((True ∨ p3) → False) → False) := by
          intro assump_53
          have assump_140 : (True ∨ p3) := by
            apply Or.inl
            apply True.intro
          let assump_56 := assump_53 assump_140
          apply False.elim assump_56
        let assump_52 := assump_3 assump_139
        apply False.elim assump_52
      case inr assump_47 =>
        cases assump_47
        case intro assump_63 assump_64 =>
          cases assump_63
          case inl assump_65 =>
            cases assump_64
            case inl assump_69 =>
              have assump_141 : (((True ∨ p3) → False) → False) := by
                intro assump_76
                have assump_142 : (True ∨ p3) := by
                  apply Or.inl
                  apply True.intro
                let assump_79 := assump_76 assump_142
                apply False.elim assump_79
              let assump_75 := assump_3 assump_141
              apply False.elim assump_75
            case inr assump_70 =>
              have assump_143 : (((True ∨ p3) → False) → False) := by
                intro assump_91
                have assump_144 : (True ∨ p3) := by
                  apply Or.inl
                  apply True.intro
                let assump_94 := assump_91 assump_144
                apply False.elim assump_94
              let assump_90 := assump_3 assump_143
              apply False.elim assump_90
          case inr assump_66 =>
            cases assump_64
            case inl assump_103 =>
              have assump_145 : (((True ∨ p3) → False) → False) := by
                intro assump_110
                have assump_146 : (True ∨ p3) := by
                  apply Or.inl
                  apply True.intro
                let assump_113 := assump_110 assump_146
                apply False.elim assump_113
              let assump_109 := assump_3 assump_145
              apply False.elim assump_109
            case inr assump_104 =>
              have assump_147 : (((True ∨ p3) → False) → False) := by
                intro assump_125
                have assump_148 : (True ∨ p3) := by
                  apply Or.inl
                  apply True.intro
                let assump_128 := assump_125 assump_148
                apply False.elim assump_128
              let assump_124 := assump_3 assump_147
              apply False.elim assump_124


variable (p2 p5 p6 p3 p1 p4 : Prop)
theorem file50_65593 : (((((p6 ∧ False) → False) → False) → False) ∨ ((((p2 ∨ p3) ∨ (p6 → p2)) ∨ ((p2 ∧ p1) ∧ (p2 → p5))) ∨ (((True ∨ p2) ∨ (p1 ∨ p1)) → ((p2 ∨ True) → (p4 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p6 ∧ False) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p2 p7 p6 p5 p1 p3 : Prop)
theorem file50_66072 : (((((p5 → p5) → False) ∧ ((p1 ∧ p2) → False)) → False) ∨ ((((p2 ∧ p5) ∧ (p7 ∧ p3)) → ((p0 → False) → False)) ∨ (((False → p6) ∧ (False → False)) ∧ ((False ∨ p5) ∨ (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (p5 → p5) := by
      intro assump_10
      exact assump_10
    let assump_9 := assump_2 assump_16
    apply False.elim assump_9


variable (p0 p6 p7 p1 p2 p4 p5 : Prop)
theorem file50_66554 : (((((p4 ∨ p1) ∧ (p2 ∨ p2)) ∧ ((p5 → p5) → (p2 → False))) ∧ (((p7 ∨ p1) ∨ (p7 → p7)) → ((True ∧ True) ∧ (p4 ∧ p5)))) → ((((p1 ∧ True) → False) ∨ ((p0 → False) ∨ (p6 ∨ p1))) ∨ (((p4 → True) ∧ (False ∨ False)) → ((p4 ∧ p5) ∨ (p4 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_7
          case inl assump_12 =>
            apply Or.inl
            apply Or.inl
            intro assump_20
            cases assump_20
            case intro assump_21 assump_22 =>
              have assump_138 : (p5 → p5) := by
                intro assump_37
                exact assump_37
              let assump_36 := assump_5 assump_138
              have assump_139 : p2 := by
                exact assump_12
              let assump_40 := assump_36 assump_139
              apply False.elim assump_40
          case inr assump_13 =>
            apply Or.inl
            apply Or.inl
            intro assump_50
            cases assump_50
            case intro assump_51 assump_52 =>
              have assump_140 : (p5 → p5) := by
                intro assump_67
                exact assump_67
              let assump_66 := assump_5 assump_140
              have assump_141 : p2 := by
                exact assump_13
              let assump_70 := assump_66 assump_141
              apply False.elim assump_70
        case inr assump_9 =>
          cases assump_7
          case inl assump_76 =>
            apply Or.inl
            apply Or.inl
            intro assump_84
            cases assump_84
            case intro assump_85 assump_86 =>
              have assump_142 : (p5 → p5) := by
                intro assump_101
                exact assump_101
              let assump_100 := assump_5 assump_142
              have assump_143 : p2 := by
                exact assump_76
              let assump_104 := assump_100 assump_143
              apply False.elim assump_104
          case inr assump_77 =>
            apply Or.inl
            apply Or.inl
            intro assump_114
            cases assump_114
            case intro assump_115 assump_116 =>
              have assump_144 : (p5 → p5) := by
                intro assump_131
                exact assump_131
              let assump_130 := assump_5 assump_144
              have assump_145 : p2 := by
                exact assump_77
              let assump_134 := assump_130 assump_145
              apply False.elim assump_134


variable (p1 p4 p0 : Prop)
theorem file50_69231 : (((((False → p4) ∧ (p1 ∧ False)) → ((p0 → True) → False)) → (((p0 ∧ p0) → (p1 ∨ True)) → False)) → False) := by
  intro assump_14
  have assump_43 : (((False → p4) ∧ (p1 ∧ False)) → ((p0 → True) → False)) := by
    intro assump_18
    intro assump_19
    cases assump_18
    case intro assump_22 assump_23 =>
      cases assump_23
      case intro assump_26 assump_27 =>
        apply False.elim assump_27
  let assump_17 := assump_14 assump_43
  have assump_44 : ((p0 ∧ p0) → (p1 ∨ True)) := by
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      apply Or.inr
      apply True.intro
  let assump_32 := assump_17 assump_44
  apply False.elim assump_32


variable (p0 p6 p1 p4 p2 p5 : Prop)
theorem file50_69975 : (((((p0 ∧ p6) → (False → False)) ∨ ((p5 → False) ∧ (True → p0))) → (((False → p4) ∨ (p4 ∨ False)) → False)) → ((((p5 → False) → False) ∧ ((p2 ∧ p1) → (True ∧ False))) ∨ (((p1 ∧ p5) ∨ (False ∨ False)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_41 : (((p0 ∧ p6) → (False → False)) ∨ ((p5 → False) ∧ (True → p0))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_8 := assump_1 assump_41
  have assump_42 : ((False → p4) ∨ (p4 ∨ False)) := by
    apply Or.inl
    intro assump_14
    apply False.elim assump_14
  let assump_13 := assump_8 assump_42
  apply False.elim assump_13
  intro assump_20
  apply And.intro
  apply True.intro
  cases assump_20
  case intro assump_21 assump_22 =>
    have assump_43 : (((p0 ∧ p6) → (False → False)) ∨ ((p5 → False) ∧ (True → p0))) := by
      apply Or.inl
      intro assump_30
      intro assump_31
      apply False.elim assump_31
    let assump_29 := assump_1 assump_43
    have assump_44 : ((False → p4) ∨ (p4 ∨ False)) := by
      apply Or.inl
      intro assump_35
      apply False.elim assump_35
    let assump_34 := assump_29 assump_44
    apply False.elim assump_34


variable (p4 p3 p6 p1 p5 p7 p2 : Prop)
theorem file50_71262 : ((((((True → False) ∨ (p2 ∨ p5)) ∧ ((p3 → p1) → (False ∨ p4))) ∨ (((p6 ∨ True) ∧ (p3 → False)) ∨ ((p2 ∧ False) → False))) ∧ ((((p7 → p7) ∧ (p2 → p1)) → False) ∧ (((False ∧ p7) ∧ (p7 ∨ p1)) ∧ ((p1 ∧ p7) → False)))) → False) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_16
        case inl assump_18 =>
          cases assump_13
          case intro assump_24 assump_25 =>
            cases assump_25
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
        case inr assump_19 =>
          cases assump_19
          case inl assump_36 =>
            cases assump_13
            case intro assump_42 assump_43 =>
              cases assump_43
              case intro assump_46 assump_47 =>
                cases assump_46
                case intro assump_48 assump_49 =>
                  cases assump_48
                  case intro assump_50 assump_51 =>
                    apply False.elim assump_50
          case inr assump_37 =>
            cases assump_13
            case intro assump_58 assump_59 =>
              cases assump_59
              case intro assump_62 assump_63 =>
                cases assump_62
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case intro assump_66 assump_67 =>
                    apply False.elim assump_66
    case inr assump_15 =>
      cases assump_15
      case inl assump_70 =>
        cases assump_70
        case intro assump_72 assump_73 =>
          cases assump_72
          case inl assump_74 =>
            cases assump_13
            case intro assump_80 assump_81 =>
              cases assump_81
              case intro assump_84 assump_85 =>
                cases assump_84
                case intro assump_86 assump_87 =>
                  cases assump_86
                  case intro assump_88 assump_89 =>
                    apply False.elim assump_88
          case inr assump_75 =>
            cases assump_13
            case intro assump_96 assump_97 =>
              cases assump_97
              case intro assump_100 assump_101 =>
                cases assump_100
                case intro assump_102 assump_103 =>
                  cases assump_102
                  case intro assump_104 assump_105 =>
                    apply False.elim assump_104
      case inr assump_71 =>
        cases assump_13
        case intro assump_110 assump_111 =>
          cases assump_111
          case intro assump_114 assump_115 =>
            cases assump_114
            case intro assump_116 assump_117 =>
              cases assump_116
              case intro assump_118 assump_119 =>
                apply False.elim assump_118


variable (p1 p3 p2 p4 p7 p0 : Prop)
theorem file50_74334 : (((((p1 → False) → (False → p3)) ∨ ((p2 ∧ p7) → False)) → False) → ((((p7 → p7) ∨ (p4 ∨ False)) → False) → (((False ∨ p1) → (p7 → p4)) ∨ ((False → p7) ∧ (False ∧ p0))))) := by
  intro assump_5
  intro assump_6
  apply Or.inl
  intro assump_11
  intro assump_12
  cases assump_11
  case inl assump_15 =>
    apply False.elim assump_15
  case inr assump_16 =>
    have assump_31 : (((p1 → False) → (False → p3)) ∨ ((p2 ∧ p7) → False)) := by
      apply Or.inl
      intro assump_24
      intro assump_25
      apply False.elim assump_25
    let assump_23 := assump_5 assump_31
    apply False.elim assump_23


variable (p4 p5 p6 p7 p2 p0 : Prop)
theorem file50_75000 : (((((p0 → p2) → False) ∧ ((p7 → False) ∨ (False ∧ p4))) ∧ (((p7 ∧ p4) ∧ (True ∧ True)) ∧ ((p0 ∧ p7) ∧ (p5 ∧ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                cases assump_13
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_29
                    case intro assump_36 assump_37 =>
                      have assump_56 : p7 := by
                        exact assump_31
                      let assump_48 := assump_8 assump_56
                      apply False.elim assump_48
      case inr assump_9 =>
        cases assump_9
        case intro assump_52 assump_53 =>
          apply False.elim assump_52


variable (p2 p0 p3 p6 p4 p5 : Prop)
theorem file50_76230 : (((((p0 ∨ False) → (p0 ∨ True)) ∨ ((p3 ∨ p2) ∨ (p0 → False))) ∨ (((p4 ∧ True) → (p4 ∨ p6)) → False)) → ((((False → False) ∨ (p5 → False)) ∨ ((p4 ∨ False) ∧ (p2 → False))) ∨ (((p2 → p5) → (p5 → False)) ∨ ((p0 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      intro assump_8
      apply False.elim assump_8
    case inr assump_5 =>
      cases assump_5
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_17
          apply False.elim assump_17
        case inr assump_14 =>
          apply Or.inl
          apply Or.inl
          apply Or.inl
          intro assump_22
          apply False.elim assump_22
      case inr assump_12 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        intro assump_27
        apply False.elim assump_27
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_32
    apply False.elim assump_32


variable (p0 p7 p5 p3 p1 p2 : Prop)
theorem file50_77433 : (((((p5 → p3) ∧ (False → p1)) ∨ ((False ∨ p2) → (False → False))) ∧ (((p2 ∧ False) ∧ (p0 ∧ p3)) ∧ ((p7 → p5) ∧ (p3 → False)))) → False) := by
  intro assump_15
  cases assump_15
  case intro assump_16 assump_17 =>
    cases assump_16
    case inl assump_18 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_17
        case intro assump_26 assump_27 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            cases assump_28
            case intro assump_30 assump_31 =>
              apply False.elim assump_31
    case inr assump_19 =>
      cases assump_17
      case intro assump_38 assump_39 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_43


variable (p7 p4 p0 p6 p2 p3 p1 : Prop)
theorem file50_78332 : ((((((p0 ∧ True) ∨ (p4 ∨ True)) ∨ ((p0 ∧ p3) → (p1 → True))) ∨ (((p7 ∧ p6) ∨ (p2 ∨ p7)) ∧ ((p1 → p3) ∨ (p0 ∧ p7)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p0 ∧ True) ∨ (p4 ∨ True)) ∨ ((p0 ∧ p3) → (p1 → True))) ∨ (((p7 ∧ p6) ∨ (p2 ∨ p7)) ∧ ((p1 → p3) ∨ (p0 ∧ p7)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p0 p3 p7 p2 p6 p1 : Prop)
theorem file50_78843 : (((((p7 → False) ∨ (p7 ∧ p3)) → False) → (((False ∧ True) → False) ∨ ((p4 → p1) ∧ (False ∧ False)))) ∨ ((((p1 → p2) ∧ (p4 ∧ p2)) → ((True → p0) ∧ (p3 → False))) → (((p6 ∧ p0) ∧ (p4 ∨ p7)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p7 p5 p1 p4 p3 p2 p6 : Prop)
theorem file50_79256 : (((((False ∧ True) ∨ (False ∨ p3)) → False) → (((p2 ∧ True) → False) → ((False → p1) ∧ (True → True)))) ∨ ((((p2 → p3) → (p1 ∨ p1)) → ((p5 ∧ p4) → False)) ∧ (((p1 → p1) → False) ∨ ((p6 → p5) ∧ (p7 → p4))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  apply False.elim assump_3
  intro assump_6
  apply True.intro


variable (p7 p0 p4 p2 p1 p5 p3 : Prop)
theorem file50_79680 : (((((p0 → False) → (p2 ∨ p4)) ∨ ((p7 ∨ p5) → False)) ∨ (((p4 → p1) → False) → ((False → False) ∧ (p0 → p1)))) → ((((p3 → False) ∧ (p5 ∧ p7)) → ((True ∨ False) → (p2 ∧ p3))) → (((p4 ∧ p3) → False) → ((p3 ∨ p0) → (False → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p0 p4 p6 p5 : Prop)
theorem file50_80084 : (((((p5 ∨ p4) → (p0 → p6)) → ((p0 → True) ∨ (p4 → p0))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p5 ∨ p4) → (p0 → p6)) → ((p0 → True) ∨ (p4 → p0))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p3 p0 p1 p7 p4 p6 : Prop)
theorem file50_80461 : (((((p6 ∧ p4) ∧ (p7 ∨ p7)) ∧ ((p7 ∨ p4) ∧ (p1 → False))) ∧ (((p7 → False) ∨ (p1 ∨ p3)) ∧ ((False ∧ p4) → (p6 ∧ p6)))) ∨ ((((p6 → p6) → (True ∨ p6)) → False) → (((True → False) ∧ (p0 → False)) → False))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_18 : ((p6 → p6) → (True ∨ p6)) := by
      intro assump_12
      apply Or.inl
      apply True.intro
    let assump_11 := assump_1 assump_18
    apply False.elim assump_11


variable (p1 p7 p5 p3 p6 p0 : Prop)
theorem file50_81018 : ((((((p1 ∨ False) → False) → ((False → False) ∨ (p7 → p0))) ∨ (((p5 ∨ False) → (True → False)) ∨ ((p1 ∧ p6) ∧ (p3 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 ∨ False) → False) → ((False → False) ∨ (p7 → p0))) ∨ (((p5 ∨ False) → (True → False)) ∨ ((p1 ∧ p6) ∧ (p3 ∨ p1)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p0 p7 p1 p6 p5 p3 p4 : Prop)
theorem file50_81561 : (((((p6 ∧ False) ∧ (p0 ∨ p1)) ∧ ((p3 ∧ p1) → False)) ∧ (((p2 ∧ p6) → False) → False)) ∨ ((((p4 → p0) → (True ∨ p5)) → False) → (((p5 ∨ True) ∨ (p0 ∨ p4)) → ((p0 → p4) ∨ (True ∨ p7))))) := by
  apply Or.inr
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      intro assump_11
      have assump_61 : ((p4 → p0) → (True ∨ p5)) := by
        intro assump_16
        apply Or.inl
        apply True.intro
      let assump_15 := assump_1 assump_61
      apply False.elim assump_15
    case inr assump_6 =>
      apply Or.inl
      intro assump_26
      have assump_62 : ((p4 → p0) → (True ∨ p5)) := by
        intro assump_31
        apply Or.inl
        apply True.intro
      let assump_30 := assump_1 assump_62
      apply False.elim assump_30
  case inr assump_4 =>
    cases assump_4
    case inl assump_37 =>
      apply Or.inl
      intro assump_43
      have assump_63 : ((p4 → p0) → (True ∨ p5)) := by
        intro assump_48
        apply Or.inl
        apply True.intro
      let assump_47 := assump_1 assump_63
      apply False.elim assump_47
    case inr assump_38 =>
      apply Or.inl
      intro assump_58
      exact assump_38


variable (p0 p3 p2 p4 p1 : Prop)
theorem file50_82847 : (((((p2 → True) → (p0 → False)) ∧ ((p4 ∧ p1) ∧ (p4 ∧ p1))) ∧ (((True ∨ p3) → False) ∨ ((p4 → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_3
            case inl assump_22 =>
              have assump_39 : (True ∨ p3) := by
                apply Or.inl
                apply True.intro
              let assump_26 := assump_22 assump_39
              apply False.elim assump_26
            case inr assump_23 =>
              have assump_40 : (p4 → p1) := by
                intro assump_33
                exact assump_17
              let assump_32 := assump_23 assump_40
              apply False.elim assump_32


variable (p7 p2 p3 p5 p6 p0 : Prop)
theorem file50_83847 : ((((((p3 ∨ True) ∨ (p6 → False)) ∧ ((False → False) → False)) → (((p7 ∧ True) → False) ∧ ((p5 → False) → False))) ∧ ((((True ∧ False) → (p0 → False)) → False) ∧ (((p2 → p7) ∨ (p6 → p5)) ∨ ((False ∨ p7) → (p7 ∧ p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_65 : ((True ∧ False) → (p0 → False)) := by
            intro assump_18
            intro assump_19
            cases assump_18
            case intro assump_22 assump_23 =>
              apply False.elim assump_23
          let assump_17 := assump_6 assump_65
          apply False.elim assump_17
        case inr assump_13 =>
          have assump_66 : ((True ∧ False) → (p0 → False)) := by
            intro assump_35
            intro assump_36
            cases assump_35
            case intro assump_39 assump_40 =>
              apply False.elim assump_40
          let assump_34 := assump_6 assump_66
          apply False.elim assump_34
      case inr assump_11 =>
        have assump_67 : ((True ∧ False) → (p0 → False)) := by
          intro assump_52
          intro assump_53
          cases assump_52
          case intro assump_56 assump_57 =>
            apply False.elim assump_57
        let assump_51 := assump_6 assump_67
        apply False.elim assump_51


variable (p7 p5 p1 p6 p3 p4 p0 p2 : Prop)
theorem file50_85371 : (((((p2 ∨ p2) → (p1 → p0)) → ((p1 ∧ p6) ∨ (p7 → False))) ∧ (((p5 ∧ p6) → False) ∧ ((p5 ∨ p6) ∧ (p5 → False)))) → ((((True → p1) → False) ∧ ((False → p6) ∨ (p7 → p3))) → (((p5 ∧ True) → False) ∨ ((p4 ∨ p0) ∧ (p1 → p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              apply Or.inl
              intro assump_27
              cases assump_27
              case intro assump_28 assump_29 =>
                have assump_101 : p5 := by
                  exact assump_28
                let assump_35 := assump_20 assump_101
                apply False.elim assump_35
            case inr assump_22 =>
              apply Or.inl
              intro assump_43
              cases assump_43
              case intro assump_44 assump_45 =>
                have assump_102 : p5 := by
                  exact assump_44
                let assump_51 := assump_20 assump_102
                apply False.elim assump_51
    case inr assump_8 =>
      cases assump_1
      case intro assump_57 assump_58 =>
        cases assump_58
        case intro assump_61 assump_62 =>
          cases assump_62
          case intro assump_65 assump_66 =>
            cases assump_65
            case inl assump_67 =>
              apply Or.inl
              intro assump_73
              cases assump_73
              case intro assump_74 assump_75 =>
                have assump_103 : p5 := by
                  exact assump_74
                let assump_81 := assump_66 assump_103
                apply False.elim assump_81
            case inr assump_68 =>
              apply Or.inl
              intro assump_89
              cases assump_89
              case intro assump_90 assump_91 =>
                have assump_104 : p5 := by
                  exact assump_90
                let assump_97 := assump_66 assump_104
                apply False.elim assump_97


variable (p5 p7 p3 p1 p4 p6 : Prop)
theorem file50_87634 : ((((((p1 ∨ p7) ∨ (p6 → p5)) ∧ ((p1 ∨ True) ∧ (p3 ∧ p5))) ∧ (((p7 ∧ False) ∧ (p5 ∨ p6)) → ((p6 → False) ∨ (p4 → False)))) ∧ ((((p3 ∨ p5) → False) → False) ∧ (((p4 → p4) ∨ (True → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_7
            case intro assump_14 assump_15 =>
              cases assump_14
              case inl assump_16 =>
                cases assump_15
                case intro assump_20 assump_21 =>
                  cases assump_3
                  case intro assump_28 assump_29 =>
                    have assump_168 : ((p4 → p4) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_35
                      exact assump_35
                    let assump_34 := assump_29 assump_168
                    apply False.elim assump_34
              case inr assump_17 =>
                cases assump_15
                case intro assump_43 assump_44 =>
                  cases assump_3
                  case intro assump_51 assump_52 =>
                    have assump_169 : ((p4 → p4) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_58
                      exact assump_58
                    let assump_57 := assump_52 assump_169
                    apply False.elim assump_57
          case inr assump_11 =>
            cases assump_7
            case intro assump_66 assump_67 =>
              cases assump_66
              case inl assump_68 =>
                cases assump_67
                case intro assump_72 assump_73 =>
                  cases assump_3
                  case intro assump_80 assump_81 =>
                    have assump_170 : ((p4 → p4) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_87
                      exact assump_87
                    let assump_86 := assump_81 assump_170
                    apply False.elim assump_86
              case inr assump_69 =>
                cases assump_67
                case intro assump_95 assump_96 =>
                  cases assump_3
                  case intro assump_103 assump_104 =>
                    have assump_171 : ((p4 → p4) ∨ (True → False)) := by
                      apply Or.inl
                      intro assump_110
                      exact assump_110
                    let assump_109 := assump_104 assump_171
                    apply False.elim assump_109
        case inr assump_9 =>
          cases assump_7
          case intro assump_118 assump_119 =>
            cases assump_118
            case inl assump_120 =>
              cases assump_119
              case intro assump_124 assump_125 =>
                cases assump_3
                case intro assump_132 assump_133 =>
                  have assump_172 : ((p4 → p4) ∨ (True → False)) := by
                    apply Or.inl
                    intro assump_139
                    exact assump_139
                  let assump_138 := assump_133 assump_172
                  apply False.elim assump_138
            case inr assump_121 =>
              cases assump_119
              case intro assump_147 assump_148 =>
                cases assump_3
                case intro assump_155 assump_156 =>
                  have assump_173 : ((p4 → p4) ∨ (True → False)) := by
                    apply Or.inl
                    intro assump_162
                    exact assump_162
                  let assump_161 := assump_156 assump_173
                  apply False.elim assump_161


variable (p0 p1 p4 : Prop)
theorem file50_91492 : (((((p0 → True) ∨ (p1 → False)) ∨ ((p1 → p1) ∨ (p0 ∨ p4))) → False) → False) := by
  intro assump_1
  have assump_9 : (((p0 → True) ∨ (p1 → False)) ∨ ((p1 → p1) ∨ (p0 ∨ p4))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p3 p7 p6 p0 p2 p4 : Prop)
theorem file50_91871 : (((((p7 → p7) → False) → ((p6 ∨ p6) → (p4 → p2))) → False) → ((((p2 ∧ False) → False) ∨ ((p0 ∧ p6) → (p3 → False))) ∨ (((p7 ∨ p0) ∧ (p0 → True)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_6


variable (p7 p4 p6 p3 p2 p5 : Prop)
theorem file50_92238 : (((((p3 → False) ∨ (p4 ∨ False)) ∨ ((p6 ∨ False) → False)) ∧ (((True ∨ p5) ∧ (p5 → False)) ∨ ((p4 ∨ p2) → (p7 → False)))) → ((((p6 → p4) → (p6 ∧ p2)) ∧ ((p7 → False) ∧ (p5 ∧ False))) → (((p2 → p6) ∧ (p3 → False)) ∧ ((p3 → False) → False)))) := by
  intro assump_7
  intro assump_8
  apply And.intro
  apply And.intro
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_17
      case intro assump_20 assump_21 =>
        apply False.elim assump_21
  intro assump_26
  cases assump_8
  case intro assump_29 assump_30 =>
    cases assump_30
    case intro assump_33 assump_34 =>
      cases assump_34
      case intro assump_37 assump_38 =>
        apply False.elim assump_38
  intro assump_43
  cases assump_8
  case intro assump_46 assump_47 =>
    cases assump_47
    case intro assump_50 assump_51 =>
      cases assump_51
      case intro assump_54 assump_55 =>
        apply False.elim assump_55


variable (p2 p6 p4 p1 p5 p0 p3 p7 : Prop)
theorem file50_93298 : (((((p1 → False) → False) ∧ ((p7 ∧ False) ∧ (p6 → False))) ∧ (((p5 ∨ p4) ∧ (p4 → False)) → ((p5 → False) ∨ (p4 ∨ p2)))) → ((((p2 ∧ p0) ∨ (p2 → False)) ∧ ((p4 → True) ∨ (p3 ∧ p3))) ∨ (((False ∨ p0) ∧ (p1 ∨ p3)) → ((False → False) → (p5 ∧ p1))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_11


variable (p1 p7 p3 p2 p6 p0 p5 p4 : Prop)
theorem file50_93899 : (((((False ∧ p3) ∧ (p2 → p3)) ∧ ((p6 ∨ p6) ∧ (p7 ∨ p6))) → (((p5 ∨ p0) ∧ (p2 ∧ p1)) → ((p4 ∨ p6) ∧ (p0 → False)))) ∨ ((((True ∨ p6) ∧ (p2 ∨ p0)) ∧ ((p4 → False) ∧ (p4 → False))) → (((p1 ∧ p5) ∧ (True → False)) → ((p6 → False) → (p7 → p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              apply False.elim assump_19
    case inr assump_6 =>
      cases assump_4
      case intro assump_25 assump_26 =>
        cases assump_1
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            cases assump_33
            case intro assump_35 assump_36 =>
              apply False.elim assump_35
  intro assump_39
  cases assump_2
  case intro assump_42 assump_43 =>
    cases assump_42
    case inl assump_44 =>
      cases assump_43
      case intro assump_48 assump_49 =>
        cases assump_1
        case intro assump_54 assump_55 =>
          cases assump_54
          case intro assump_56 assump_57 =>
            cases assump_56
            case intro assump_58 assump_59 =>
              apply False.elim assump_58
    case inr assump_45 =>
      cases assump_43
      case intro assump_64 assump_65 =>
        cases assump_1
        case intro assump_70 assump_71 =>
          cases assump_70
          case intro assump_72 assump_73 =>
            cases assump_72
            case intro assump_74 assump_75 =>
              apply False.elim assump_74


variable (p7 p3 p4 p0 p6 p5 p2 : Prop)
theorem file50_95785 : (((((p6 ∧ False) → False) ∧ ((False → False) → False)) → False) ∨ ((((True ∧ p6) ∧ (p4 ∧ p6)) ∨ ((p2 ∧ p4) ∨ (p7 ∧ p4))) ∨ (((p5 ∧ p4) ∨ (p0 → p3)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p1 p5 p3 p0 p2 p4 p6 : Prop)
theorem file50_96261 : (((((p3 ∨ p2) → (p2 → False)) → False) ∧ (((False ∨ False) → (p1 → p0)) → ((p2 ∧ p5) → (p6 ∧ p4)))) → ((((p0 → False) ∨ (p5 ∨ p3)) ∧ ((False ∧ p6) ∧ (p4 → p3))) → (((False → p3) ∨ (p2 ∨ p0)) ∧ ((p3 → p3) ∧ (p2 ∧ p5))))) := by
  intro assump_13
  intro assump_14
  apply And.intro
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      cases assump_16
      case intro assump_21 assump_22 =>
        cases assump_21
        case intro assump_23 assump_24 =>
          apply False.elim assump_23
    case inr assump_18 =>
      cases assump_18
      case inl assump_27 =>
        cases assump_16
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
      case inr assump_28 =>
        cases assump_16
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            apply False.elim assump_41
  apply And.intro
  intro assump_45
  cases assump_14
  case intro assump_48 assump_49 =>
    cases assump_48
    case inl assump_50 =>
      cases assump_49
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          apply False.elim assump_56
    case inr assump_51 =>
      cases assump_51
      case inl assump_60 =>
        cases assump_49
        case intro assump_64 assump_65 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            apply False.elim assump_66
      case inr assump_61 =>
        cases assump_49
        case intro assump_72 assump_73 =>
          cases assump_72
          case intro assump_74 assump_75 =>
            apply False.elim assump_74
  apply And.intro
  cases assump_14
  case intro assump_78 assump_79 =>
    cases assump_78
    case inl assump_80 =>
      cases assump_79
      case intro assump_84 assump_85 =>
        cases assump_84
        case intro assump_86 assump_87 =>
          apply False.elim assump_86
    case inr assump_81 =>
      cases assump_81
      case inl assump_90 =>
        cases assump_79
        case intro assump_94 assump_95 =>
          cases assump_94
          case intro assump_96 assump_97 =>
            apply False.elim assump_96
      case inr assump_91 =>
        cases assump_79
        case intro assump_102 assump_103 =>
          cases assump_102
          case intro assump_104 assump_105 =>
            apply False.elim assump_104
  cases assump_14
  case intro assump_108 assump_109 =>
    cases assump_108
    case inl assump_110 =>
      cases assump_109
      case intro assump_114 assump_115 =>
        cases assump_114
        case intro assump_116 assump_117 =>
          apply False.elim assump_116
    case inr assump_111 =>
      cases assump_111
      case inl assump_120 =>
        cases assump_109
        case intro assump_124 assump_125 =>
          cases assump_124
          case intro assump_126 assump_127 =>
            apply False.elim assump_126
      case inr assump_121 =>
        cases assump_109
        case intro assump_132 assump_133 =>
          cases assump_132
          case intro assump_134 assump_135 =>
            apply False.elim assump_134


variable (p7 p5 : Prop)
theorem file50_99554 : (((((True ∧ False) ∧ (p5 ∧ p7)) → False) → False) → False) := by
  intro assump_1
  have assump_17 : (((True ∧ False) ∧ (p5 ∧ p7)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p6 p3 p2 p5 p7 p4 : Prop)
theorem file50_99992 : (((((True → False) → (False ∧ True)) ∨ ((p7 ∨ p4) ∧ (p3 → False))) ∨ (((p6 → p3) ∨ (False ∧ p5)) ∨ ((p7 → False) ∨ (p2 → False)))) ∨ ((((p7 ∧ p6) ∧ (True → p4)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4
  apply True.intro


variable (p1 p0 p3 p4 p5 p2 p6 p7 : Prop)
theorem file50_100457 : (((((p0 ∧ True) → (p1 → False)) ∧ ((p5 ∧ p2) → (p1 → p3))) ∧ (((p1 → False) → (p0 ∨ p7)) ∧ ((True ∧ True) → False))) → ((((p0 ∨ p6) ∧ (p5 → False)) → False) → (((p4 → False) → (p3 → p5)) ∨ ((True ∧ p6) ∧ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_6
      case intro assump_13 assump_14 =>
        apply Or.inl
        intro assump_19
        intro assump_20
        have assump_31 : (True ∧ True) := by
          apply And.intro
          apply True.intro
          apply True.intro
        let assump_27 := assump_14 assump_31
        apply False.elim assump_27


variable (p4 p0 : Prop)
theorem file50_101207 : (((((True ∧ p4) → False) → ((False ∨ p0) → (p4 → False))) → False) → False) := by
  intro assump_1
  have assump_25 : (((True ∧ p4) → False) → ((False ∨ p0) → (p4 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      have assump_26 : (True ∧ p4) := by
        apply And.intro
        apply True.intro
        exact assump_7
      let assump_18 := assump_5 assump_26
      apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p1 p4 p0 p2 p7 p6 : Prop)
theorem file50_101864 : ((((((p2 → False) ∨ (p7 → p6)) → ((p6 → p1) ∨ (p3 ∧ p1))) → False) ∧ ((((p1 → False) ∧ (p2 ∧ p1)) → ((p3 ∨ True) → (p7 ∧ p1))) → (((p0 → p1) → (p4 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_82 : (((p1 → False) ∧ (p2 ∧ p1)) → ((p3 ∨ True) → (p7 ∧ p1))) := by
      intro assump_9
      intro assump_10
      apply And.intro
      cases assump_10
      case inl assump_11 =>
        cases assump_9
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            have assump_83 : p1 := by
              exact assump_20
            let assump_27 := assump_15 assump_83
            apply False.elim assump_27
      case inr assump_12 =>
        cases assump_9
        case intro assump_33 assump_34 =>
          cases assump_34
          case intro assump_37 assump_38 =>
            have assump_84 : p1 := by
              exact assump_38
            let assump_45 := assump_33 assump_84
            apply False.elim assump_45
      cases assump_10
      case inl assump_49 =>
        cases assump_9
        case intro assump_53 assump_54 =>
          cases assump_54
          case intro assump_57 assump_58 =>
            exact assump_58
      case inr assump_50 =>
        cases assump_9
        case intro assump_65 assump_66 =>
          cases assump_66
          case intro assump_69 assump_70 =>
            exact assump_70
    let assump_8 := assump_3 assump_82
    have assump_85 : ((p0 → p1) → (p4 ∨ True)) := by
      intro assump_76
      apply Or.inr
      apply True.intro
    let assump_75 := assump_8 assump_85
    apply False.elim assump_75


variable (p3 p6 p2 p5 : Prop)
theorem file50_103608 : ((((((False → p2) → False) → False) ∨ (((p2 ∨ p5) → (p5 ∧ p3)) → ((p5 → p6) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p2) → False) → False) ∨ (((p2 ∨ p5) → (p5 ∧ p3)) → ((p5 → p6) → False))) := by
    apply Or.inl
    intro assump_5
    have assump_19 : (False → p2) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


