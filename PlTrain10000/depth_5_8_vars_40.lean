variable (p6 p5 p2 p4 p3 p7 : Prop)
theorem file40_44 : (((((p3 ∧ p7) ∨ (p5 ∧ p7)) ∨ ((p6 ∨ p5) → False)) ∧ (((False ∧ p3) → (p4 → p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          have assump_64 : ((False ∧ p3) → (p4 → p2)) := by
            intro assump_17
            intro assump_18
            cases assump_17
            case intro assump_21 assump_22 =>
              apply False.elim assump_21
          let assump_16 := assump_3 assump_64
          apply False.elim assump_16
      case inr assump_7 =>
        cases assump_7
        case intro assump_28 assump_29 =>
          have assump_65 : ((False ∧ p3) → (p4 → p2)) := by
            intro assump_37
            intro assump_38
            cases assump_37
            case intro assump_41 assump_42 =>
              apply False.elim assump_41
          let assump_36 := assump_3 assump_65
          apply False.elim assump_36
    case inr assump_5 =>
      have assump_66 : ((False ∧ p3) → (p4 → p2)) := by
        intro assump_53
        intro assump_54
        cases assump_53
        case intro assump_57 assump_58 =>
          apply False.elim assump_57
      let assump_52 := assump_3 assump_66
      apply False.elim assump_52


variable (p1 p5 p0 p2 p3 p7 : Prop)
theorem file40_1459 : ((((((True ∨ p1) ∨ (p1 ∨ p0)) ∨ ((p2 → False) → (True ∧ p3))) ∨ (((p7 → False) → (p1 ∨ p2)) ∧ ((p5 ∨ False) → False))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p1) ∨ (p1 ∨ p0)) ∨ ((p2 → False) → (True ∧ p3))) ∨ (((p7 → False) → (p1 ∨ p2)) ∧ ((p5 ∨ False) → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p1 p6 p0 p3 p4 : Prop)
theorem file40_1973 : (((((True ∨ p3) ∧ (True → False)) → False) → False) → ((((p2 → False) ∧ (False → p4)) ∨ ((p0 → p6) → (p1 → True))) ∨ (((p0 ∧ p2) ∨ (p4 ∧ p6)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_4
  have assump_36 : (((True ∨ p3) ∧ (True → False)) → False) := by
    intro assump_9
    cases assump_9
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        have assump_37 : True := by
          apply True.intro
        let assump_18 := assump_11 assump_37
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_38 : True := by
          apply True.intro
        let assump_26 := assump_11 assump_38
        apply False.elim assump_26
  let assump_8 := assump_1 assump_36
  apply False.elim assump_8
  intro assump_33
  apply False.elim assump_33


variable (p6 p4 p5 p3 p2 p1 p7 : Prop)
theorem file40_2895 : (((((False → False) ∨ (p3 ∧ p1)) ∨ ((p1 → True) ∨ (p1 ∧ p1))) ∧ (((False → p6) ∨ (p7 → False)) → ((p3 ∨ True) ∧ (p4 → False)))) → ((((True → False) → (p2 → p1)) ∨ ((p6 ∧ p4) ∨ (p3 ∧ p4))) ∨ (((p7 ∧ p2) ∨ (p6 ∨ p6)) ∧ ((p5 → False) → (p6 ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        apply Or.inl
        intro assump_12
        intro assump_13
        have assump_66 : True := by
          apply True.intro
        let assump_18 := assump_12 assump_66
        apply False.elim assump_18
      case inr assump_7 =>
        cases assump_7
        case intro assump_22 assump_23 =>
          apply Or.inl
          apply Or.inl
          intro assump_30
          intro assump_31
          exact assump_23
    case inr assump_5 =>
      cases assump_5
      case inl assump_36 =>
        apply Or.inl
        apply Or.inl
        intro assump_42
        intro assump_43
        have assump_67 : True := by
          apply True.intro
        let assump_48 := assump_42 assump_67
        apply False.elim assump_48
      case inr assump_37 =>
        cases assump_37
        case intro assump_52 assump_53 =>
          apply Or.inl
          apply Or.inl
          intro assump_60
          intro assump_61
          exact assump_53


variable (p6 p1 p2 p0 p5 p3 p7 : Prop)
theorem file40_4345 : (((((p6 ∧ p2) ∨ (True ∧ p1)) ∧ ((p5 → False) → False)) → (((p2 ∨ p7) ∧ (True → False)) → ((p2 → p0) → False))) → ((((False → p2) → False) → False) ∨ (((True ∧ p1) → False) → ((p5 → p3) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (False → p2) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p2 p7 p4 p5 p1 p6 p0 : Prop)
theorem file40_4812 : (((((p1 → p4) → False) ∧ ((False ∧ p7) ∧ (p2 ∨ p0))) → False) ∨ ((((False ∧ p1) → False) ∨ ((p1 ∧ p2) ∨ (False ∧ False))) ∨ (((p6 → False) ∨ (p0 → False)) ∧ ((p2 ∧ p5) → (p1 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8


variable (p2 p1 p5 p0 : Prop)
theorem file40_5290 : ((((((False → False) ∨ (p0 ∧ p5)) → False) → (((False → p1) → (p2 ∨ p0)) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → False) ∨ (p0 ∧ p5)) → False) → (((False → p1) → (p2 ∨ p0)) ∨ ((p0 → False) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_23 : ((False → False) ∨ (p0 ∧ p5)) := by
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_5 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p2 p1 p6 p5 p3 p4 p7 : Prop)
theorem file40_5942 : (((((p0 ∨ p4) ∧ (True → False)) → ((True → p3) → (p7 ∨ p6))) ∧ (((p3 ∨ p0) ∧ (p5 ∧ p2)) → ((False → False) ∧ (False ∨ p2)))) ∨ ((((p4 → False) → False) ∧ ((p3 ∧ p6) → (False → p7))) ∧ (((p0 → p6) → (p1 ∧ p1)) → ((p7 ∧ p7) → False)))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_49 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_49
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_50 : True := by
        apply True.intro
      let assump_21 := assump_6 assump_50
      apply False.elim assump_21
  intro assump_25
  apply And.intro
  intro assump_26
  apply False.elim assump_26
  cases assump_25
  case intro assump_29 assump_30 =>
    cases assump_29
    case inl assump_31 =>
      cases assump_30
      case intro assump_35 assump_36 =>
        apply Or.inr
        exact assump_36
    case inr assump_32 =>
      cases assump_30
      case intro assump_43 assump_44 =>
        apply Or.inr
        exact assump_44


variable (p6 p4 p0 p2 : Prop)
theorem file40_7114 : (((((True ∨ p2) → False) ∨ ((p6 → True) ∧ (p0 ∧ False))) ∧ (((p4 ∧ False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_31 : ((p4 ∧ False) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          apply False.elim assump_13
      let assump_10 := assump_3 assump_31
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_21 assump_22 =>
        cases assump_22
        case intro assump_25 assump_26 =>
          apply False.elim assump_26


variable (p3 p6 p4 p1 p2 p5 p7 : Prop)
theorem file40_7840 : ((((((False ∨ p3) → False) → ((p2 ∨ p1) → (False → False))) → False) ∧ ((((p6 ∨ p1) ∨ (p2 ∧ True)) ∨ ((p5 ∧ p3) ∧ (p7 ∧ p1))) → (((p4 → True) → (p7 → p6)) ∧ ((p3 ∧ p6) → (p6 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((False ∨ p3) → False) → ((p2 ∨ p1) → (False → False))) := by
      intro assump_10
      intro assump_11
      intro assump_12
      apply False.elim assump_12
    let assump_9 := assump_2 assump_18
    apply False.elim assump_9


variable (p4 p5 p2 p0 p1 p6 : Prop)
theorem file40_8422 : ((((((p6 ∧ p5) ∨ (True ∨ p2)) → False) → (((p0 ∧ p5) ∨ (p0 ∨ p4)) ∨ ((False ∨ p1) ∧ (p4 → p5)))) → False) → False) := by
  intro assump_28
  have assump_42 : ((((p6 ∧ p5) ∨ (True ∨ p2)) → False) → (((p0 ∧ p5) ∨ (p0 ∨ p4)) ∨ ((False ∨ p1) ∧ (p4 → p5)))) := by
    intro assump_32
    have assump_43 : ((p6 ∧ p5) ∨ (True ∨ p2)) := by
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_35 := assump_32 assump_43
    apply False.elim assump_35
  let assump_31 := assump_28 assump_42
  apply False.elim assump_31


variable (p3 p0 p1 p2 p7 p6 p4 : Prop)
theorem file40_9018 : (((((p3 ∧ p4) → False) ∨ ((True → False) → (p1 → p7))) → (((p0 → p0) → False) → ((p2 ∨ p6) ∨ (p6 → p6)))) ∨ ((((p3 ∨ p1) ∨ (p0 ∨ p2)) ∨ ((p6 → False) ∨ (p6 → p0))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inr
    intro assump_9
    exact assump_9
  case inr assump_6 =>
    apply Or.inr
    intro assump_14
    exact assump_14


variable (p5 p0 p7 p4 : Prop)
theorem file40_9476 : ((((((p5 ∧ p5) → False) → ((p7 → False) ∧ (True ∧ p0))) → (((True → False) → False) ∨ ((False ∨ p4) → (p4 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 ∧ p5) → False) → ((p7 → False) ∧ (True ∧ p0))) → (((True → False) → False) ∨ ((False ∨ p4) → (p4 ∨ p4)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p1 p3 p2 p5 : Prop)
theorem file40_10073 : ((((((p2 → p3) → False) → ((p3 ∧ p1) → False)) ∨ (((p1 → False) → (True → False)) ∨ ((False → p7) ∧ (p5 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p2 → p3) → False) → ((p3 ∧ p1) → False)) ∨ (((p1 → False) → (True → False)) ∨ ((False → p7) ∧ (p5 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      have assump_26 : (p2 → p3) := by
        intro assump_16
        exact assump_7
      let assump_15 := assump_5 assump_26
      apply False.elim assump_15
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p7 p1 p5 p4 p0 : Prop)
theorem file40_10756 : (((((p5 → p5) → (False → False)) → ((p4 ∧ p1) ∧ (p1 ∨ p7))) → (((p7 ∨ p0) → (False → False)) ∨ ((p1 → False) → (p7 → False)))) ∨ ((((True ∨ p7) → (p5 → False)) ∧ ((p4 → p4) ∨ (p0 → False))) → (((p7 ∨ p7) → (p0 → True)) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p3 p2 p0 : Prop)
theorem file40_11152 : ((((((p2 ∨ p0) → False) ∧ ((True ∧ p2) ∧ (p3 ∧ p0))) → False) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p2 ∨ p0) → False) ∧ ((True ∧ p2) ∧ (p3 ∧ p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            have assump_35 : (p2 ∨ p0) := by
              apply Or.inl
              exact assump_13
            let assump_27 := assump_6 assump_35
            apply False.elim assump_27
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p4 p6 p3 p1 p5 : Prop)
theorem file40_11922 : ((((((p1 → True) → (False → False)) ∨ ((p1 ∧ p3) → (p6 → False))) ∧ (((False ∧ p5) → (p3 ∧ False)) ∧ ((p4 → False) → (True → True)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 → True) → (False → False)) ∨ ((p1 ∧ p3) → (p6 → False))) ∧ (((False ∧ p5) → (p3 ∧ False)) ∧ ((p4 → False) → (True → True)))) := by
    apply And.intro
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
    apply And.intro
    intro assump_9
    apply And.intro
    cases assump_9
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
    cases assump_9
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
    intro assump_18
    intro assump_19
    apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p0 p4 p2 p6 p3 : Prop)
theorem file40_12784 : ((((((p2 ∧ p5) ∧ (p0 ∨ p3)) → False) ∧ (((p6 → p2) → False) ∨ ((p2 ∨ p3) → (p2 → False)))) ∧ ((((True → p6) → (p6 ∨ p4)) → ((False → False) ∨ (False → p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_38 : (((True → p6) → (p6 ∨ p4)) → ((False → False) ∨ (False → p4))) := by
          intro assump_15
          apply Or.inl
          intro assump_18
          apply False.elim assump_18
        let assump_14 := assump_3 assump_38
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_39 : (((True → p6) → (p6 ∨ p4)) → ((False → False) ∨ (False → p4))) := by
          intro assump_29
          apply Or.inl
          intro assump_32
          apply False.elim assump_32
        let assump_28 := assump_3 assump_39
        apply False.elim assump_28


variable (p7 p0 p4 p6 p5 p2 : Prop)
theorem file40_13794 : ((((((p5 → False) → (p4 → True)) ∨ ((p7 ∨ p0) → (p4 ∨ p6))) → False) ∧ ((((False ∧ p4) ∨ (p7 → p2)) ∨ ((p0 ∨ p4) → False)) ∨ (((p2 ∧ p2) ∨ (p5 ∨ p0)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
        case inr assump_11 =>
          have assump_43 : (((p5 → False) → (p4 → True)) ∨ ((p7 ∨ p0) → (p4 ∨ p6))) := by
            apply Or.inl
            intro assump_20
            intro assump_21
            apply True.intro
          let assump_19 := assump_2 assump_43
          apply False.elim assump_19
      case inr assump_9 =>
        have assump_44 : (((p5 → False) → (p4 → True)) ∨ ((p7 ∨ p0) → (p4 ∨ p6))) := by
          apply Or.inl
          intro assump_29
          intro assump_30
          apply True.intro
        let assump_28 := assump_2 assump_44
        apply False.elim assump_28
    case inr assump_7 =>
      have assump_45 : (((p5 → False) → (p4 → True)) ∨ ((p7 ∨ p0) → (p4 ∨ p6))) := by
        apply Or.inl
        intro assump_38
        intro assump_39
        apply True.intro
      let assump_37 := assump_2 assump_45
      apply False.elim assump_37


variable (p2 p6 p3 p1 p0 p4 : Prop)
theorem file40_15241 : ((((((p6 → False) ∧ (p2 ∧ p6)) → ((p1 → p3) ∧ (p3 → p4))) ∨ (((False → p3) → (p4 ∨ p4)) ∧ ((p0 → False) → (False → False)))) → False) → False) := by
  intro assump_54
  have assump_100 : ((((p6 → False) ∧ (p2 ∧ p6)) → ((p1 → p3) ∧ (p3 → p4))) ∨ (((False → p3) → (p4 ∨ p4)) ∧ ((p0 → False) → (False → False)))) := by
    apply Or.inl
    intro assump_58
    apply And.intro
    intro assump_59
    cases assump_58
    case intro assump_62 assump_63 =>
      cases assump_63
      case intro assump_66 assump_67 =>
        have assump_101 : p6 := by
          exact assump_67
        let assump_74 := assump_62 assump_101
        apply False.elim assump_74
    intro assump_78
    cases assump_58
    case intro assump_81 assump_82 =>
      cases assump_82
      case intro assump_85 assump_86 =>
        have assump_102 : p6 := by
          exact assump_86
        let assump_93 := assump_81 assump_102
        apply False.elim assump_93
  let assump_57 := assump_54 assump_100
  apply False.elim assump_57


variable (p4 p2 p0 p7 p5 p3 p1 : Prop)
theorem file40_16310 : (((((p1 ∨ p2) → False) → False) ∧ (((p1 ∧ p5) ∧ (p1 → False)) ∧ ((p4 → p3) ∧ (p7 ∨ p0)))) → ((((p5 → False) ∧ (p5 ∧ p1)) → ((p5 → False) ∧ (False → False))) → (((p3 ∧ p2) → (p7 → p3)) → False))) := by
  intro assump_44
  intro assump_45
  intro assump_46
  cases assump_44
  case intro assump_51 assump_52 =>
    cases assump_52
    case intro assump_55 assump_56 =>
      cases assump_55
      case intro assump_57 assump_58 =>
        cases assump_57
        case intro assump_59 assump_60 =>
          cases assump_56
          case intro assump_67 assump_68 =>
            cases assump_68
            case inl assump_71 =>
              have assump_89 : p1 := by
                exact assump_59
              let assump_77 := assump_58 assump_89
              apply False.elim assump_77
            case inr assump_72 =>
              have assump_90 : p1 := by
                exact assump_59
              let assump_85 := assump_58 assump_90
              apply False.elim assump_85


variable (p1 p5 p2 p3 p7 p4 p0 p6 : Prop)
theorem file40_17365 : (((((p6 ∧ p4) ∨ (p7 ∨ p2)) → False) → (((p1 ∨ p3) ∨ (p5 ∨ p7)) ∨ ((p2 → p6) ∨ (p6 ∧ True)))) ∨ ((((p6 ∨ p2) → (True → p1)) ∨ ((p2 ∧ False) ∧ (p1 ∧ p1))) ∧ (((p0 → False) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_4
  have assump_12 : ((p6 ∧ p4) ∨ (p7 ∨ p2)) := by
    apply Or.inr
    apply Or.inr
    exact assump_4
  let assump_8 := assump_1 assump_12
  apply False.elim assump_8


variable (p4 : Prop)
theorem file40_17852 : ((((((False ∧ p4) → False) → False) → False) → False) → False) := by
  intro assump_13
  have assump_32 : ((((False ∧ p4) → False) → False) → False) := by
    intro assump_17
    have assump_33 : ((False ∧ p4) → False) := by
      intro assump_21
      cases assump_21
      case intro assump_22 assump_23 =>
        apply False.elim assump_22
    let assump_20 := assump_17 assump_33
    apply False.elim assump_20
  let assump_16 := assump_13 assump_32
  apply False.elim assump_16


variable (p6 p2 p3 p4 p0 p7 : Prop)
theorem file40_18396 : (((((False ∧ p2) → False) → False) ∧ (((p6 → False) ∨ (p4 → p3)) ∨ ((p3 ∧ p7) ∧ (p0 ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        have assump_61 : ((False ∧ p2) → False) := by
          intro assump_14
          cases assump_14
          case intro assump_15 assump_16 =>
            apply False.elim assump_15
        let assump_13 := assump_2 assump_61
        apply False.elim assump_13
      case inr assump_9 =>
        have assump_62 : ((False ∧ p2) → False) := by
          intro assump_26
          cases assump_26
          case intro assump_27 assump_28 =>
            apply False.elim assump_27
        let assump_25 := assump_2 assump_62
        apply False.elim assump_25
    case inr assump_7 =>
      cases assump_7
      case intro assump_34 assump_35 =>
        cases assump_34
        case intro assump_36 assump_37 =>
          cases assump_35
          case intro assump_42 assump_43 =>
            have assump_63 : ((False ∧ p2) → False) := by
              intro assump_53
              cases assump_53
              case intro assump_54 assump_55 =>
                apply False.elim assump_54
            let assump_52 := assump_2 assump_63
            apply False.elim assump_52


variable (p2 p5 p4 p1 p0 p7 p6 : Prop)
theorem file40_19808 : ((((((p5 ∨ True) ∧ (p4 ∧ p4)) → ((p1 → False) → (True ∧ p7))) ∨ (((p1 ∧ p7) → False) → False)) ∧ ((((p2 ∧ p6) ∨ (p1 → p6)) → ((p4 ∨ p4) → False)) ∧ (((p0 → True) → False) ∧ ((False ∨ p4) ∧ (p7 → p2))))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_13
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            cases assump_20
            case inl assump_22 =>
              apply False.elim assump_22
            case inr assump_23 =>
              have assump_64 : (p0 → True) := by
                intro assump_33
                apply True.intro
              let assump_32 := assump_16 assump_64
              apply False.elim assump_32
    case inr assump_9 =>
      cases assump_7
      case intro assump_39 assump_40 =>
        cases assump_40
        case intro assump_43 assump_44 =>
          cases assump_44
          case intro assump_47 assump_48 =>
            cases assump_47
            case inl assump_49 =>
              apply False.elim assump_49
            case inr assump_50 =>
              have assump_65 : (p0 → True) := by
                intro assump_60
                apply True.intro
              let assump_59 := assump_43 assump_65
              apply False.elim assump_59


variable (p7 p2 p0 p3 : Prop)
theorem file40_21297 : ((((((p0 → p2) → False) → ((p2 ∧ p7) → False)) ∨ (((p7 → p0) ∨ (p3 ∧ p7)) → False)) → False) → False) := by
  intro assump_5
  have assump_29 : ((((p0 → p2) → False) → ((p2 ∧ p7) → False)) ∨ (((p7 → p0) ∨ (p3 ∧ p7)) → False)) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      have assump_30 : (p0 → p2) := by
        intro assump_20
        exact assump_11
      let assump_19 := assump_9 assump_30
      apply False.elim assump_19
  let assump_8 := assump_5 assump_29
  apply False.elim assump_8


variable (p7 p5 p3 p4 p0 : Prop)
theorem file40_21927 : (((((False → False) → (p4 ∧ p0)) → False) ∧ (((True → p0) → (True → False)) ∧ ((False ∨ p3) → False))) → ((((p7 → False) ∧ (p5 ∨ True)) → ((p0 → True) ∨ (p3 → False))) ∨ (((p3 → False) → False) ∧ ((p4 → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply Or.inl
          intro assump_21
          apply True.intro
        case inr assump_18 =>
          apply Or.inl
          intro assump_24
          apply True.intro


variable (p5 p4 p6 p1 p7 p2 p0 p3 : Prop)
theorem file40_22683 : (((((False ∧ p0) → (p5 → False)) → False) → (((p5 ∧ True) → (p1 ∨ False)) ∨ ((p6 ∧ p3) ∨ (p7 ∨ False)))) ∨ ((((p0 → False) → False) ∧ ((p5 ∧ p1) ∨ (p7 → False))) → (((p1 → p4) ∨ (p2 ∧ p6)) → ((p4 → p2) → (p0 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_24 : ((False ∧ p0) → (p5 → False)) := by
      intro assump_13
      intro assump_14
      cases assump_13
      case intro assump_17 assump_18 =>
        apply False.elim assump_17
    let assump_12 := assump_1 assump_24
    apply False.elim assump_12


variable (p0 p2 p5 p6 p1 p7 : Prop)
theorem file40_23351 : ((((((p7 → False) → (p5 → True)) ∨ ((p6 → False) ∧ (p7 ∨ p1))) ∨ (((p0 → p2) → (True ∨ p0)) ∨ ((p1 ∨ False) → False))) → False) → False) := by
  intro assump_1
  have assump_10 : ((((p7 → False) → (p5 → True)) ∨ ((p6 → False) ∧ (p7 ∨ p1))) ∨ (((p0 → p2) → (True ∨ p0)) ∨ ((p1 ∨ False) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p3 p5 p0 p4 p2 : Prop)
theorem file40_23868 : (((((p4 ∧ p5) → (p5 ∨ False)) → False) → False) ∨ ((((p3 ∧ True) ∧ (p4 ∨ False)) → ((p0 → False) → False)) ∨ (((p2 → False) ∨ (p5 → False)) → False))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p4 ∧ p5) → (p5 ∨ False)) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      exact assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p2 p3 p1 p7 p4 : Prop)
theorem file40_24348 : ((((((p4 ∨ p1) ∨ (p1 → p2)) → False) → (((p6 → False) ∧ (p7 ∨ p3)) → False)) → False) → False) := by
  intro assump_1
  have assump_48 : ((((p4 ∨ p1) ∨ (p1 → p2)) → False) → (((p6 → False) ∧ (p7 ∨ p3)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_8
      case inl assump_11 =>
        have assump_49 : ((p4 ∨ p1) ∨ (p1 → p2)) := by
          apply Or.inr
          intro assump_18
          have assump_50 : ((p4 ∨ p1) ∨ (p1 → p2)) := by
            apply Or.inl
            apply Or.inr
            exact assump_18
          let assump_22 := assump_5 assump_50
          apply False.elim assump_22
        let assump_17 := assump_5 assump_49
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_51 : ((p4 ∨ p1) ∨ (p1 → p2)) := by
          apply Or.inr
          intro assump_34
          have assump_52 : ((p4 ∨ p1) ∨ (p1 → p2)) := by
            apply Or.inl
            apply Or.inr
            exact assump_34
          let assump_38 := assump_5 assump_52
          apply False.elim assump_38
        let assump_33 := assump_5 assump_51
        apply False.elim assump_33
  let assump_4 := assump_1 assump_48
  apply False.elim assump_4


variable (p1 p7 p4 p5 : Prop)
theorem file40_25657 : ((((((True → True) → False) ∧ ((False ∨ p4) ∨ (True ∨ False))) → (((p4 ∧ p5) → False) ∨ ((p7 → p1) ∧ (p7 ∨ p5)))) → False) → False) := by
  intro assump_18
  have assump_73 : ((((True → True) → False) ∧ ((False ∨ p4) ∨ (True ∨ False))) → (((p4 ∧ p5) → False) ∨ ((p7 → p1) ∧ (p7 ∨ p5)))) := by
    intro assump_22
    cases assump_22
    case intro assump_23 assump_24 =>
      cases assump_24
      case inl assump_27 =>
        cases assump_27
        case inl assump_29 =>
          apply False.elim assump_29
        case inr assump_30 =>
          apply Or.inl
          intro assump_35
          cases assump_35
          case intro assump_36 assump_37 =>
            have assump_74 : (True → True) := by
              intro assump_46
              apply True.intro
            let assump_45 := assump_23 assump_74
            apply False.elim assump_45
      case inr assump_28 =>
        cases assump_28
        case inl assump_50 =>
          apply Or.inl
          intro assump_54
          cases assump_54
          case intro assump_55 assump_56 =>
            have assump_75 : (True → True) := by
              intro assump_64
              apply True.intro
            let assump_63 := assump_23 assump_75
            apply False.elim assump_63
        case inr assump_51 =>
          apply False.elim assump_51
  let assump_21 := assump_18 assump_73
  apply False.elim assump_21


variable (p7 p4 p5 p3 p1 p2 p6 : Prop)
theorem file40_27113 : (((((True → False) ∨ (p6 ∨ p4)) → ((p3 ∧ p1) → (p3 → False))) ∧ (((p5 → p3) → (p4 ∧ p2)) ∧ ((False → p3) → False))) → ((((p6 → p7) → False) → False) → (((p6 → False) ∧ (False → False)) ∨ ((p6 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      apply Or.inl
      apply And.intro
      intro assump_15
      have assump_29 : (False → p3) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_10 assump_29
      apply False.elim assump_19
      intro assump_26
      apply False.elim assump_26


variable (p4 p7 p5 p2 p1 p3 p0 : Prop)
theorem file40_27831 : (((((p5 ∨ p7) ∧ (p4 → p2)) → ((p7 → p1) → (p4 → False))) ∧ (((p4 → False) → False) ∧ ((False ∧ False) ∨ (p4 → p1)))) → ((((p1 ∧ p1) ∧ (p5 → False)) ∨ ((p0 ∨ p3) → (p0 ∧ p0))) → (((p1 ∧ False) → (p1 ∨ p1)) ∨ ((p0 ∨ p3) → (False → p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_16
          case intro assump_19 assump_20 =>
            cases assump_20
            case inl assump_23 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                apply False.elim assump_25
            case inr assump_24 =>
              apply Or.inl
              intro assump_31
              cases assump_31
              case intro assump_32 assump_33 =>
                apply False.elim assump_33
  case inr assump_4 =>
    cases assump_1
    case intro assump_40 assump_41 =>
      cases assump_41
      case intro assump_44 assump_45 =>
        cases assump_45
        case inl assump_48 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            apply False.elim assump_50
        case inr assump_49 =>
          apply Or.inl
          intro assump_56
          cases assump_56
          case intro assump_57 assump_58 =>
            apply False.elim assump_58


variable (p4 p1 p6 p7 p3 p5 : Prop)
theorem file40_29345 : ((((((p4 ∨ p7) → False) ∧ ((p1 → p3) → False)) ∧ (((p3 ∧ p3) ∧ (True → False)) ∧ ((p5 → False) → False))) ∧ ((((p1 ∨ False) ∧ (False ∨ p3)) ∨ ((False ∨ p3) ∨ (False ∨ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              have assump_32 : (((p1 ∨ False) ∧ (False ∨ p3)) ∨ ((False ∨ p3) ∨ (False ∨ p6))) := by
                apply Or.inr
                apply Or.inl
                apply Or.inr
                exact assump_17
              let assump_28 := assump_3 assump_32
              apply False.elim assump_28


variable (p2 p0 p7 p4 p6 p3 p5 p1 : Prop)
theorem file40_30311 : ((((((True → False) → False) → ((p3 → False) ∨ (p2 → False))) ∨ (((p1 ∧ p7) ∨ (p0 → False)) → ((p1 → p5) → (p4 ∧ True)))) ∧ ((((p4 → True) → (True → False)) → ((p6 ∧ p7) → False)) → False)) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      have assump_71 : (((p4 → True) → (True → False)) → ((p6 ∧ p7) → False)) := by
        intro assump_28
        intro assump_29
        cases assump_29
        case intro assump_30 assump_31 =>
          have assump_72 : (p4 → True) := by
            intro assump_39
            apply True.intro
          let assump_38 := assump_28 assump_72
          have assump_73 : True := by
            apply True.intro
          let assump_40 := assump_38 assump_73
          apply False.elim assump_40
      let assump_27 := assump_20 assump_71
      apply False.elim assump_27
    case inr assump_22 =>
      have assump_74 : (((p4 → True) → (True → False)) → ((p6 ∧ p7) → False)) := by
        intro assump_52
        intro assump_53
        cases assump_53
        case intro assump_54 assump_55 =>
          have assump_75 : (p4 → True) := by
            intro assump_63
            apply True.intro
          let assump_62 := assump_52 assump_75
          have assump_76 : True := by
            apply True.intro
          let assump_64 := assump_62 assump_76
          apply False.elim assump_64
      let assump_51 := assump_20 assump_74
      apply False.elim assump_51


variable (p1 p7 p2 p6 p0 p5 p4 : Prop)
theorem file40_31871 : (((((p7 ∨ p4) ∧ (p1 ∨ p4)) ∧ ((True → False) ∧ (p4 ∨ p2))) → False) ∧ ((((True → False) ∧ (p6 ∨ p5)) ∨ ((p2 ∧ False) ∧ (p6 ∨ p0))) → (((p7 ∧ False) → False) ∨ ((False ∧ p2) → (p7 → False))))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_3
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              have assump_139 : True := by
                apply True.intro
              let assump_23 := assump_14 assump_139
              apply False.elim assump_23
            case inr assump_19 =>
              have assump_140 : True := by
                apply True.intro
              let assump_30 := assump_14 assump_140
              apply False.elim assump_30
        case inr assump_11 =>
          cases assump_3
          case intro assump_36 assump_37 =>
            cases assump_37
            case inl assump_40 =>
              have assump_141 : True := by
                apply True.intro
              let assump_45 := assump_36 assump_141
              apply False.elim assump_45
            case inr assump_41 =>
              have assump_142 : True := by
                apply True.intro
              let assump_52 := assump_36 assump_142
              apply False.elim assump_52
      case inr assump_7 =>
        cases assump_5
        case inl assump_58 =>
          cases assump_3
          case intro assump_62 assump_63 =>
            cases assump_63
            case inl assump_66 =>
              have assump_143 : True := by
                apply True.intro
              let assump_71 := assump_62 assump_143
              apply False.elim assump_71
            case inr assump_67 =>
              have assump_144 : True := by
                apply True.intro
              let assump_78 := assump_62 assump_144
              apply False.elim assump_78
        case inr assump_59 =>
          cases assump_3
          case intro assump_84 assump_85 =>
            cases assump_85
            case inl assump_88 =>
              have assump_145 : True := by
                apply True.intro
              let assump_93 := assump_84 assump_145
              apply False.elim assump_93
            case inr assump_89 =>
              have assump_146 : True := by
                apply True.intro
              let assump_100 := assump_84 assump_146
              apply False.elim assump_100
  intro assump_104
  cases assump_104
  case inl assump_105 =>
    cases assump_105
    case intro assump_107 assump_108 =>
      cases assump_108
      case inl assump_111 =>
        apply Or.inl
        intro assump_115
        cases assump_115
        case intro assump_116 assump_117 =>
          apply False.elim assump_117
      case inr assump_112 =>
        apply Or.inl
        intro assump_124
        cases assump_124
        case intro assump_125 assump_126 =>
          apply False.elim assump_126
  case inr assump_106 =>
    cases assump_106
    case intro assump_131 assump_132 =>
      cases assump_131
      case intro assump_133 assump_134 =>
        apply False.elim assump_134


variable (p3 p6 p2 p0 p1 p5 : Prop)
theorem file40_35223 : ((((((p2 ∨ True) → (p1 ∧ p5)) → ((p3 ∧ p2) → (p3 ∨ True))) ∨ (((p6 ∧ p0) → False) ∨ ((p2 → p2) ∧ (p6 ∨ p2)))) → False) → False) := by
  intro assump_16
  have assump_33 : ((((p2 ∨ True) → (p1 ∧ p5)) → ((p3 ∧ p2) → (p3 ∨ True))) ∨ (((p6 ∧ p0) → False) ∨ ((p2 → p2) ∧ (p6 ∨ p2)))) := by
    apply Or.inl
    intro assump_20
    intro assump_21
    cases assump_21
    case intro assump_22 assump_23 =>
      apply Or.inl
      exact assump_22
  let assump_19 := assump_16 assump_33
  apply False.elim assump_19


variable (p1 p6 p4 : Prop)
theorem file40_35783 : ((((((p1 ∨ p1) → False) → False) → (((p1 → False) ∨ (True → False)) → ((p6 → p4) → (True ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 ∨ p1) → False) → False) → (((p1 → False) ∨ (True → False)) → ((p6 → p4) → (True ∨ False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_6
    case inl assump_10 =>
      apply Or.inl
      apply True.intro
    case inr assump_11 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p1 p3 p7 p6 p0 : Prop)
theorem file40_36386 : ((((((True ∧ p2) ∨ (p6 → True)) ∨ ((p7 ∧ p6) ∧ (p0 → False))) → False) ∨ ((((p6 → p0) → (p1 → p3)) → ((False → p6) → False)) ∧ (((p0 ∨ p6) ∨ (p1 ∧ True)) → False))) → False) := by
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    have assump_44 : (((True ∧ p2) ∨ (p6 → True)) ∨ ((p7 ∧ p6) ∧ (p0 → False))) := by
      apply Or.inl
      apply Or.inr
      intro assump_13
      apply True.intro
    let assump_12 := assump_8 assump_44
    apply False.elim assump_12
  case inr assump_9 =>
    cases assump_9
    case intro assump_17 assump_18 =>
      have assump_45 : ((p6 → p0) → (p1 → p3)) := by
        intro assump_25
        intro assump_26
        have assump_46 : ((p0 ∨ p6) ∨ (p1 ∧ True)) := by
          apply Or.inr
          apply And.intro
          exact assump_26
          apply True.intro
        let assump_33 := assump_18 assump_46
        apply False.elim assump_33
      let assump_24 := assump_17 assump_45
      have assump_47 : (False → p6) := by
        intro assump_38
        apply False.elim assump_38
      let assump_37 := assump_24 assump_47
      apply False.elim assump_37


variable (p3 p2 p5 p1 p7 p6 p0 p4 : Prop)
theorem file40_37569 : (((((True ∨ p6) ∧ (False ∧ p4)) ∧ ((p2 ∨ p3) → (p1 → False))) → (((p7 → p1) ∧ (p2 ∧ p0)) ∨ ((p2 → False) → (p3 ∨ p3)))) ∨ ((((p1 → p7) ∧ (p1 ∧ p4)) → ((p1 → True) → False)) ∧ (((p0 ∧ False) → (p3 ∧ p7)) ∨ ((p0 ∧ p4) → (p5 → p1))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
      case inr assump_7 =>
        cases assump_5
        case intro assump_16 assump_17 =>
          apply False.elim assump_16


variable (p7 p0 p1 p5 p4 p3 p6 : Prop)
theorem file40_38287 : (((((p5 → p0) ∧ (p1 → p3)) → False) ∧ (((p6 ∧ p6) ∧ (p3 → False)) ∧ ((p5 → False) ∧ (p1 → False)))) → ((((p0 → False) ∧ (False ∨ p3)) ∨ ((p4 ∧ True) ∧ (p7 → False))) → (((p3 → False) → False) → ((p6 → False) ∧ (p6 → p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_12
      case inl assump_15 =>
        apply False.elim assump_15
      case inr assump_16 =>
        cases assump_1
        case intro assump_21 assump_22 =>
          cases assump_22
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              cases assump_27
              case intro assump_29 assump_30 =>
                cases assump_26
                case intro assump_37 assump_38 =>
                  have assump_210 : p3 := by
                    exact assump_16
                  let assump_45 := assump_28 assump_210
                  apply False.elim assump_45
  case inr assump_10 =>
    cases assump_10
    case intro assump_49 assump_50 =>
      cases assump_49
      case intro assump_51 assump_52 =>
        cases assump_1
        case intro assump_59 assump_60 =>
          cases assump_60
          case intro assump_63 assump_64 =>
            cases assump_63
            case intro assump_65 assump_66 =>
              cases assump_65
              case intro assump_67 assump_68 =>
                cases assump_64
                case intro assump_75 assump_76 =>
                  have assump_211 : ((p5 → p0) ∧ (p1 → p3)) := by
                    apply And.intro
                    intro assump_87
                    have assump_212 : p5 := by
                      exact assump_87
                    let assump_92 := assump_75 assump_212
                    apply False.elim assump_92
                    intro assump_96
                    have assump_213 : p1 := by
                      exact assump_96
                    let assump_100 := assump_76 assump_213
                    apply False.elim assump_100
                  let assump_86 := assump_59 assump_211
                  apply False.elim assump_86
  intro assump_107
  cases assump_2
  case inl assump_112 =>
    cases assump_112
    case intro assump_114 assump_115 =>
      cases assump_115
      case inl assump_118 =>
        apply False.elim assump_118
      case inr assump_119 =>
        cases assump_1
        case intro assump_124 assump_125 =>
          cases assump_125
          case intro assump_128 assump_129 =>
            cases assump_128
            case intro assump_130 assump_131 =>
              cases assump_130
              case intro assump_132 assump_133 =>
                cases assump_129
                case intro assump_140 assump_141 =>
                  have assump_214 : p3 := by
                    exact assump_119
                  let assump_148 := assump_131 assump_214
                  apply False.elim assump_148
  case inr assump_113 =>
    cases assump_113
    case intro assump_152 assump_153 =>
      cases assump_152
      case intro assump_154 assump_155 =>
        cases assump_1
        case intro assump_162 assump_163 =>
          cases assump_163
          case intro assump_166 assump_167 =>
            cases assump_166
            case intro assump_168 assump_169 =>
              cases assump_168
              case intro assump_170 assump_171 =>
                cases assump_167
                case intro assump_178 assump_179 =>
                  have assump_215 : ((p5 → p0) ∧ (p1 → p3)) := by
                    apply And.intro
                    intro assump_190
                    have assump_216 : p5 := by
                      exact assump_190
                    let assump_195 := assump_178 assump_216
                    apply False.elim assump_195
                    intro assump_199
                    have assump_217 : p1 := by
                      exact assump_199
                    let assump_203 := assump_179 assump_217
                    apply False.elim assump_203
                  let assump_189 := assump_162 assump_215
                  apply False.elim assump_189


variable (p6 p0 p5 p7 p1 : Prop)
theorem file40_42601 : (((((p1 → p5) → False) ∧ ((p6 ∧ p5) ∧ (p1 ∧ p7))) ∧ (((p6 ∨ p1) ∨ (p0 → p5)) ∨ ((p6 → p6) → False))) → False) := by
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
              cases assump_22
              case inl assump_24 =>
                cases assump_24
                case inl assump_26 =>
                  have assump_79 : (p1 → p5) := by
                    intro assump_36
                    exact assump_11
                  let assump_35 := assump_4 assump_79
                  apply False.elim assump_35
                case inr assump_27 =>
                  have assump_80 : (p1 → p5) := by
                    intro assump_50
                    exact assump_11
                  let assump_49 := assump_4 assump_80
                  apply False.elim assump_49
              case inr assump_25 =>
                have assump_81 : (p1 → p5) := by
                  intro assump_64
                  exact assump_11
                let assump_63 := assump_4 assump_81
                apply False.elim assump_63
            case inr assump_23 =>
              have assump_82 : (p6 → p6) := by
                intro assump_73
                exact assump_73
              let assump_72 := assump_23 assump_82
              apply False.elim assump_72


variable (p5 p7 p1 p0 p3 p2 p4 p6 : Prop)
theorem file40_44263 : ((((((p6 ∨ p2) → (False ∧ p7)) ∧ ((p0 → p6) ∧ (p5 → p1))) ∨ (((p0 ∨ p3) ∧ (False ∧ p0)) ∧ ((True ∧ p1) ∧ (p2 → p4)))) ∧ ((((True ∧ p4) ∨ (p2 → True)) ∧ ((False ∧ p1) → (p7 → False))) → False)) → False) := by
  intro assump_24
  cases assump_24
  case intro assump_25 assump_26 =>
    cases assump_25
    case inl assump_27 =>
      cases assump_27
      case intro assump_29 assump_30 =>
        cases assump_30
        case intro assump_33 assump_34 =>
          have assump_72 : (((True ∧ p4) ∨ (p2 → True)) ∧ ((False ∧ p1) → (p7 → False))) := by
            apply And.intro
            apply Or.inr
            intro assump_42
            apply True.intro
            intro assump_43
            intro assump_44
            cases assump_43
            case intro assump_47 assump_48 =>
              apply False.elim assump_47
          let assump_41 := assump_26 assump_72
          apply False.elim assump_41
    case inr assump_28 =>
      cases assump_28
      case intro assump_54 assump_55 =>
        cases assump_54
        case intro assump_56 assump_57 =>
          cases assump_56
          case inl assump_58 =>
            cases assump_57
            case intro assump_62 assump_63 =>
              apply False.elim assump_62
          case inr assump_59 =>
            cases assump_57
            case intro assump_68 assump_69 =>
              apply False.elim assump_68


variable (p4 p2 p5 p0 p3 p7 : Prop)
theorem file40_45711 : (((((p0 ∨ True) ∨ (p5 → False)) ∨ ((p5 ∨ p4) ∨ (p7 ∨ p0))) → False) → ((((p2 ∧ p0) → (False → p3)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_11 : (((p0 ∨ True) ∨ (p5 → False)) ∨ ((p5 ∨ p4) ∨ (p7 ∨ p0))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p3 p6 p1 p4 p0 p2 : Prop)
theorem file40_46148 : (((((p3 → p3) → False) ∨ ((p2 → True) → False)) ∧ (((False ∨ p0) ∨ (p0 → False)) ∧ ((p3 ∧ p6) ∨ (p4 ∧ p1)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_9
            case inl assump_18 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                have assump_162 : (p3 → p3) := by
                  intro assump_30
                  exact assump_30
                let assump_29 := assump_4 assump_162
                apply False.elim assump_29
            case inr assump_19 =>
              cases assump_19
              case intro assump_36 assump_37 =>
                have assump_163 : (p3 → p3) := by
                  intro assump_46
                  exact assump_46
                let assump_45 := assump_4 assump_163
                apply False.elim assump_45
        case inr assump_11 =>
          cases assump_9
          case inl assump_54 =>
            cases assump_54
            case intro assump_56 assump_57 =>
              have assump_164 : (p3 → p3) := by
                intro assump_66
                exact assump_66
              let assump_65 := assump_4 assump_164
              apply False.elim assump_65
          case inr assump_55 =>
            cases assump_55
            case intro assump_72 assump_73 =>
              have assump_165 : (p3 → p3) := by
                intro assump_82
                exact assump_82
              let assump_81 := assump_4 assump_165
              apply False.elim assump_81
    case inr assump_5 =>
      cases assump_3
      case intro assump_90 assump_91 =>
        cases assump_90
        case inl assump_92 =>
          cases assump_92
          case inl assump_94 =>
            apply False.elim assump_94
          case inr assump_95 =>
            cases assump_91
            case inl assump_100 =>
              cases assump_100
              case intro assump_102 assump_103 =>
                have assump_166 : (p2 → True) := by
                  intro assump_112
                  apply True.intro
                let assump_111 := assump_5 assump_166
                apply False.elim assump_111
            case inr assump_101 =>
              cases assump_101
              case intro assump_116 assump_117 =>
                have assump_167 : (p2 → True) := by
                  intro assump_126
                  apply True.intro
                let assump_125 := assump_5 assump_167
                apply False.elim assump_125
        case inr assump_93 =>
          cases assump_91
          case inl assump_132 =>
            cases assump_132
            case intro assump_134 assump_135 =>
              have assump_168 : (p2 → True) := by
                intro assump_144
                apply True.intro
              let assump_143 := assump_5 assump_168
              apply False.elim assump_143
          case inr assump_133 =>
            cases assump_133
            case intro assump_148 assump_149 =>
              have assump_169 : (p2 → True) := by
                intro assump_158
                apply True.intro
              let assump_157 := assump_5 assump_169
              apply False.elim assump_157


variable (p0 p7 p6 p4 : Prop)
theorem file40_49698 : ((((((False ∧ p4) ∧ (False → False)) → False) ∨ (((p0 ∧ p7) → (p4 → False)) ∧ ((p6 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ p4) ∧ (False → False)) → False) ∨ (((p0 ∧ p7) → (p4 → False)) ∧ ((p6 ∧ False) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p0 p4 p1 p3 p6 : Prop)
theorem file40_50277 : (((((p0 ∨ p6) ∧ (p0 ∧ False)) ∧ ((False ∧ p3) ∨ (True ∧ p6))) → False) ∨ ((((True → False) → (p1 ∧ p7)) ∨ ((p3 → False) → (False ∨ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          apply False.elim assump_11
      case inr assump_7 =>
        cases assump_5
        case intro assump_18 assump_19 =>
          apply False.elim assump_19


variable (p4 p2 p1 p5 p3 p7 : Prop)
theorem file40_50907 : (((((True → False) → False) → False) ∧ (((p1 ∨ p2) ∧ (p2 → False)) ∧ ((False → True) → False))) → ((((True → p7) → (p5 ∧ p1)) → ((p2 → False) ∨ (p3 → False))) → (((p3 → p4) ∧ (p4 ∧ p7)) ∧ ((True ∧ p5) → False)))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  apply And.intro
  intro assump_7
  cases assump_5
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case inl assump_20 =>
          have assump_153 : (False → True) := by
            intro assump_29
            apply True.intro
          let assump_28 := assump_17 assump_153
          apply False.elim assump_28
        case inr assump_21 =>
          have assump_154 : (False → True) := by
            intro assump_40
            apply True.intro
          let assump_39 := assump_17 assump_154
          apply False.elim assump_39
  apply And.intro
  cases assump_5
  case intro assump_46 assump_47 =>
    cases assump_47
    case intro assump_50 assump_51 =>
      cases assump_50
      case intro assump_52 assump_53 =>
        cases assump_52
        case inl assump_54 =>
          have assump_155 : (False → True) := by
            intro assump_63
            apply True.intro
          let assump_62 := assump_51 assump_155
          apply False.elim assump_62
        case inr assump_55 =>
          have assump_156 : (False → True) := by
            intro assump_74
            apply True.intro
          let assump_73 := assump_51 assump_156
          apply False.elim assump_73
  cases assump_5
  case intro assump_80 assump_81 =>
    cases assump_81
    case intro assump_84 assump_85 =>
      cases assump_84
      case intro assump_86 assump_87 =>
        cases assump_86
        case inl assump_88 =>
          have assump_157 : (False → True) := by
            intro assump_97
            apply True.intro
          let assump_96 := assump_85 assump_157
          apply False.elim assump_96
        case inr assump_89 =>
          have assump_158 : (False → True) := by
            intro assump_108
            apply True.intro
          let assump_107 := assump_85 assump_158
          apply False.elim assump_107
  intro assump_112
  cases assump_112
  case intro assump_113 assump_114 =>
    cases assump_5
    case intro assump_121 assump_122 =>
      cases assump_122
      case intro assump_125 assump_126 =>
        cases assump_125
        case intro assump_127 assump_128 =>
          cases assump_127
          case inl assump_129 =>
            have assump_159 : (False → True) := by
              intro assump_138
              apply True.intro
            let assump_137 := assump_126 assump_159
            apply False.elim assump_137
          case inr assump_130 =>
            have assump_160 : (False → True) := by
              intro assump_149
              apply True.intro
            let assump_148 := assump_126 assump_160
            apply False.elim assump_148


variable (p3 p4 p2 p0 p6 p5 p1 p7 : Prop)
theorem file40_53989 : (((((p4 → False) ∧ (p4 ∧ p0)) ∧ ((p5 → p6) ∧ (p4 ∧ p6))) ∧ (((p1 → False) ∨ (p0 → False)) ∧ ((p5 ∧ p4) → (p5 → p0)))) → ((((p0 → p1) → False) ∧ ((p3 ∧ p6) ∧ (p7 → False))) → (((p3 ∧ p3) ∧ (p2 → False)) ∧ ((p6 → False) ∨ (p0 ∨ True))))) := by
  intro assump_5
  intro assump_6
  apply And.intro
  apply And.intro
  apply And.intro
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_8
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_5
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              cases assump_26
              case intro assump_29 assump_30 =>
                cases assump_24
                case intro assump_35 assump_36 =>
                  cases assump_36
                  case intro assump_39 assump_40 =>
                    cases assump_22
                    case intro assump_45 assump_46 =>
                      cases assump_45
                      case inl assump_47 =>
                        exact assump_13
                      case inr assump_48 =>
                        exact assump_13
  cases assump_6
  case intro assump_57 assump_58 =>
    cases assump_58
    case intro assump_61 assump_62 =>
      cases assump_61
      case intro assump_63 assump_64 =>
        cases assump_5
        case intro assump_71 assump_72 =>
          cases assump_71
          case intro assump_73 assump_74 =>
            cases assump_73
            case intro assump_75 assump_76 =>
              cases assump_76
              case intro assump_79 assump_80 =>
                cases assump_74
                case intro assump_85 assump_86 =>
                  cases assump_86
                  case intro assump_89 assump_90 =>
                    cases assump_72
                    case intro assump_95 assump_96 =>
                      cases assump_95
                      case inl assump_97 =>
                        exact assump_63
                      case inr assump_98 =>
                        exact assump_63
  intro assump_107
  cases assump_6
  case intro assump_110 assump_111 =>
    cases assump_111
    case intro assump_114 assump_115 =>
      cases assump_114
      case intro assump_116 assump_117 =>
        cases assump_5
        case intro assump_124 assump_125 =>
          cases assump_124
          case intro assump_126 assump_127 =>
            cases assump_126
            case intro assump_128 assump_129 =>
              cases assump_129
              case intro assump_132 assump_133 =>
                cases assump_127
                case intro assump_138 assump_139 =>
                  cases assump_139
                  case intro assump_142 assump_143 =>
                    cases assump_125
                    case intro assump_148 assump_149 =>
                      cases assump_148
                      case inl assump_150 =>
                        have assump_250 : p4 := by
                          exact assump_142
                        let assump_163 := assump_128 assump_250
                        apply False.elim assump_163
                      case inr assump_151 =>
                        have assump_251 : p0 := by
                          exact assump_133
                        let assump_172 := assump_151 assump_251
                        apply False.elim assump_172
  cases assump_6
  case intro assump_176 assump_177 =>
    cases assump_177
    case intro assump_180 assump_181 =>
      cases assump_180
      case intro assump_182 assump_183 =>
        cases assump_5
        case intro assump_190 assump_191 =>
          cases assump_190
          case intro assump_192 assump_193 =>
            cases assump_192
            case intro assump_194 assump_195 =>
              cases assump_195
              case intro assump_198 assump_199 =>
                cases assump_193
                case intro assump_204 assump_205 =>
                  cases assump_205
                  case intro assump_208 assump_209 =>
                    cases assump_191
                    case intro assump_214 assump_215 =>
                      cases assump_214
                      case inl assump_216 =>
                        apply Or.inl
                        intro assump_222
                        have assump_252 : p4 := by
                          exact assump_208
                        let assump_233 := assump_194 assump_252
                        apply False.elim assump_233
                      case inr assump_217 =>
                        apply Or.inl
                        intro assump_241
                        have assump_253 : p0 := by
                          exact assump_199
                        let assump_246 := assump_217 assump_253
                        apply False.elim assump_246


variable (p5 p4 p3 p7 p2 : Prop)
theorem file40_58986 : ((((((p3 ∧ p7) → False) → ((p5 ∧ p2) → (p2 ∧ True))) ∨ (((p4 → False) → False) → ((p5 ∨ True) ∧ (p4 ∧ p2)))) → False) → False) := by
  intro assump_5
  have assump_22 : ((((p3 ∧ p7) → False) → ((p5 ∧ p2) → (p2 ∧ True))) ∨ (((p4 → False) → False) → ((p5 ∨ True) ∧ (p4 ∧ p2)))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    apply And.intro
    cases assump_10
    case intro assump_11 assump_12 =>
      exact assump_12
    apply True.intro
  let assump_8 := assump_5 assump_22
  apply False.elim assump_8


variable (p2 p6 p4 p7 p3 p0 p5 p1 : Prop)
theorem file40_59576 : (((((p2 ∧ p5) ∧ (p6 ∧ False)) ∧ ((True → p0) ∨ (p7 → p3))) → (((p1 → False) → (p7 → False)) → False)) ∨ ((((p3 ∧ p3) ∧ (p5 ∧ p3)) → ((p6 ∧ p0) → (p5 ∧ False))) ∨ (((p6 ∧ p7) → False) ∨ ((p4 ∨ p7) ∧ (p6 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          apply False.elim assump_16


variable (p7 p2 p6 p5 : Prop)
theorem file40_60165 : (((((p6 → True) ∧ (False → p2)) ∨ ((p6 → p7) → (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p6 → True) ∧ (False → p2)) ∨ ((p6 → p7) → (p5 → False))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply True.intro
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p1 p5 p2 p7 p3 p4 p0 : Prop)
theorem file40_60610 : ((((((p6 ∧ p0) → (p1 → False)) → ((p4 → False) → False)) ∧ (((p4 → p7) ∧ (False ∧ p3)) ∧ ((p1 ∧ p4) ∧ (True → p7)))) ∧ ((((p7 ∨ False) ∨ (p5 → p2)) → False) → False)) → False) := by
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
            apply False.elim assump_14


variable (p7 p4 p5 : Prop)
theorem file40_61199 : ((((((True ∧ p5) ∧ (p7 → False)) ∧ ((False ∧ p7) ∧ (False ∨ p4))) → False) → False) → False) := by
  intro assump_8
  have assump_34 : ((((True ∧ p5) ∧ (p7 → False)) ∧ ((False ∧ p7) ∧ (False ∨ p4))) → False) := by
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_14
          case intro assump_25 assump_26 =>
            cases assump_25
            case intro assump_27 assump_28 =>
              apply False.elim assump_27
  let assump_11 := assump_8 assump_34
  apply False.elim assump_11


variable (p2 p4 p7 p6 p5 p1 : Prop)
theorem file40_61931 : (((((False → False) ∨ (p4 → p1)) ∧ ((p5 → p5) → False)) → (((p6 → False) → False) → False)) ∨ ((((p2 ∧ p7) ∧ (p6 ∨ p2)) → ((p4 → p5) → (p6 ∧ p5))) ∨ (((p4 → False) → (True → False)) ∨ ((p1 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_31 : (p5 → p5) := by
        intro assump_14
        exact assump_14
      let assump_13 := assump_6 assump_31
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_32 : (p5 → p5) := by
        intro assump_25
        exact assump_25
      let assump_24 := assump_6 assump_32
      apply False.elim assump_24


variable (p3 p4 p1 p0 p7 : Prop)
theorem file40_62697 : ((((((p3 → False) ∧ (p0 ∨ False)) ∨ ((p0 ∧ p0) → (p0 → False))) → False) ∧ ((((p4 ∨ p7) ∧ (True → False)) → ((p3 ∨ False) ∧ (p1 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_56 : (((p4 ∨ p7) ∧ (True → False)) → ((p3 ∨ False) ∧ (p1 → False))) := by
      intro assump_9
      apply And.intro
      cases assump_9
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          have assump_57 : True := by
            apply True.intro
          let assump_18 := assump_11 assump_57
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_58 : True := by
            apply True.intro
          let assump_26 := assump_11 assump_58
          apply False.elim assump_26
      intro assump_30
      cases assump_9
      case intro assump_33 assump_34 =>
        cases assump_33
        case inl assump_35 =>
          have assump_59 : True := by
            apply True.intro
          let assump_41 := assump_34 assump_59
          apply False.elim assump_41
        case inr assump_36 =>
          have assump_60 : True := by
            apply True.intro
          let assump_49 := assump_34 assump_60
          apply False.elim assump_49
    let assump_8 := assump_3 assump_56
    apply False.elim assump_8


variable (p1 p5 p4 p7 p6 p2 p3 : Prop)
theorem file40_64110 : (((((p1 → False) ∧ (p3 ∨ p4)) ∧ ((p7 ∧ p4) → (p6 → False))) ∧ (((p4 ∨ False) ∧ (p5 ∨ p1)) → False)) → ((((p2 ∨ p3) → False) ∧ ((p5 ∨ True) ∧ (p3 → False))) → (((p5 → False) ∨ (p5 → False)) ∨ ((p2 → p2) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_1
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_17
            case intro assump_19 assump_20 =>
              cases assump_20
              case inl assump_23 =>
                apply Or.inl
                apply Or.inl
                intro assump_31
                have assump_103 : p3 := by
                  exact assump_23
                let assump_39 := assump_8 assump_103
                apply False.elim assump_39
              case inr assump_24 =>
                apply Or.inl
                apply Or.inl
                intro assump_49
                have assump_104 : ((p4 ∨ False) ∧ (p5 ∨ p1)) := by
                  apply And.intro
                  apply Or.inl
                  exact assump_24
                  apply Or.inl
                  exact assump_49
                let assump_53 := assump_16 assump_104
                apply False.elim assump_53
      case inr assump_10 =>
        cases assump_1
        case intro assump_61 assump_62 =>
          cases assump_61
          case intro assump_63 assump_64 =>
            cases assump_63
            case intro assump_65 assump_66 =>
              cases assump_66
              case inl assump_69 =>
                apply Or.inl
                apply Or.inl
                intro assump_77
                have assump_105 : p3 := by
                  exact assump_69
                let assump_85 := assump_8 assump_105
                apply False.elim assump_85
              case inr assump_70 =>
                apply Or.inl
                apply Or.inl
                intro assump_95
                have assump_106 : ((p4 ∨ False) ∧ (p5 ∨ p1)) := by
                  apply And.intro
                  apply Or.inl
                  exact assump_70
                  apply Or.inl
                  exact assump_95
                let assump_99 := assump_62 assump_106
                apply False.elim assump_99


variable (p7 p4 p6 : Prop)
theorem file40_66581 : ((((((False → False) → False) ∨ ((False → p6) ∧ (False ∧ p7))) → False) → ((((p7 ∨ True) → False) → ((False ∧ p4) ∧ (True ∧ p7))) → False)) → False) := by
  intro assump_1
  have assump_48 : ((((False → False) → False) ∨ ((False → p6) ∧ (False ∧ p7))) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      have assump_49 : (False → False) := by
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_6 assump_49
      apply False.elim assump_10
    case inr assump_7 =>
      cases assump_7
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          apply False.elim assump_21
  let assump_4 := assump_1 assump_48
  have assump_50 : (((p7 ∨ True) → False) → ((False ∧ p4) ∧ (True ∧ p7))) := by
    intro assump_26
    apply And.intro
    apply And.intro
    have assump_51 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_29 := assump_26 assump_51
    apply False.elim assump_29
    have assump_52 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_35 := assump_26 assump_52
    apply False.elim assump_35
    apply And.intro
    apply True.intro
    have assump_53 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_41 := assump_26 assump_53
    apply False.elim assump_41
  let assump_25 := assump_4 assump_50
  apply False.elim assump_25


variable (p1 p7 p2 p6 p4 p5 p3 : Prop)
theorem file40_68086 : ((((((p3 ∨ p3) → False) ∨ ((False ∨ p4) → (False ∨ False))) ∧ (((p6 ∨ True) → (p2 ∨ p4)) ∧ ((p1 → p7) ∧ (p7 ∨ True)))) ∧ ((((True → True) → (p5 → p6)) → False) ∧ (((p7 ∨ p4) ∧ (False ∧ p5)) ∧ ((p3 ∧ p7) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  cases assump_26
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_29
                      case intro assump_34 assump_35 =>
                        apply False.elim assump_34
                    case inr assump_31 =>
                      cases assump_29
                      case intro assump_40 assump_41 =>
                        apply False.elim assump_40
            case inr assump_19 =>
              cases assump_3
              case intro assump_46 assump_47 =>
                cases assump_47
                case intro assump_50 assump_51 =>
                  cases assump_50
                  case intro assump_52 assump_53 =>
                    cases assump_52
                    case inl assump_54 =>
                      cases assump_53
                      case intro assump_58 assump_59 =>
                        apply False.elim assump_58
                    case inr assump_55 =>
                      cases assump_53
                      case intro assump_64 assump_65 =>
                        apply False.elim assump_64
      case inr assump_7 =>
        cases assump_5
        case intro assump_70 assump_71 =>
          cases assump_71
          case intro assump_74 assump_75 =>
            cases assump_75
            case inl assump_78 =>
              cases assump_3
              case intro assump_82 assump_83 =>
                cases assump_83
                case intro assump_86 assump_87 =>
                  cases assump_86
                  case intro assump_88 assump_89 =>
                    cases assump_88
                    case inl assump_90 =>
                      cases assump_89
                      case intro assump_94 assump_95 =>
                        apply False.elim assump_94
                    case inr assump_91 =>
                      cases assump_89
                      case intro assump_100 assump_101 =>
                        apply False.elim assump_100
            case inr assump_79 =>
              cases assump_3
              case intro assump_106 assump_107 =>
                cases assump_107
                case intro assump_110 assump_111 =>
                  cases assump_110
                  case intro assump_112 assump_113 =>
                    cases assump_112
                    case inl assump_114 =>
                      cases assump_113
                      case intro assump_118 assump_119 =>
                        apply False.elim assump_118
                    case inr assump_115 =>
                      cases assump_113
                      case intro assump_124 assump_125 =>
                        apply False.elim assump_124


variable (p4 p7 p2 p6 p5 : Prop)
theorem file40_71675 : ((((((p2 ∨ p2) → (p7 → p5)) → False) → (((p6 → False) → False) → ((p5 → False) ∨ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p2 ∨ p2) → (p7 → p5)) → False) → (((p6 → False) → False) → ((p5 → False) ∨ (p4 → False)))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    intro assump_11
    have assump_33 : ((p2 ∨ p2) → (p7 → p5)) := by
      intro assump_16
      intro assump_17
      cases assump_16
      case inl assump_20 =>
        exact assump_11
      case inr assump_21 =>
        exact assump_11
    let assump_15 := assump_5 assump_33
    apply False.elim assump_15
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p0 p4 p7 p6 p2 p5 p3 p1 : Prop)
theorem file40_72431 : ((((((True → True) → False) → ((p0 → False) → False)) ∧ (((True ∨ False) → False) ∧ ((p5 → p1) ∨ (p4 ∨ p3)))) ∧ ((((p2 → p7) ∨ (p0 → p6)) → ((p7 → p6) ∧ (True → False))) ∧ (((p0 ∧ p0) ∨ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            have assump_61 : ((p0 ∧ p0) ∨ (False → False)) := by
              apply Or.inr
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_17 assump_61
            apply False.elim assump_22
        case inr assump_13 =>
          cases assump_13
          case inl assump_29 =>
            cases assump_3
            case intro assump_33 assump_34 =>
              have assump_62 : ((p0 ∧ p0) ∨ (False → False)) := by
                apply Or.inr
                intro assump_40
                apply False.elim assump_40
              let assump_39 := assump_34 assump_62
              apply False.elim assump_39
          case inr assump_30 =>
            cases assump_3
            case intro assump_48 assump_49 =>
              have assump_63 : ((p0 ∧ p0) ∨ (False → False)) := by
                apply Or.inr
                intro assump_55
                apply False.elim assump_55
              let assump_54 := assump_49 assump_63
              apply False.elim assump_54


variable (p3 p7 p4 p0 p2 p6 p5 : Prop)
theorem file40_74070 : (((((p0 ∧ False) → False) ∨ ((True ∨ p2) ∨ (p7 → True))) ∧ (((p0 ∧ p4) → False) ∧ ((p7 ∨ p0) ∧ (False ∧ p6)))) → ((((p3 → False) ∧ (p2 ∧ p3)) ∨ ((p7 ∧ p5) ∨ (p7 ∨ False))) → (((p3 → p3) → False) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case intro assump_24 assump_25 =>
              cases assump_25
              case intro assump_28 assump_29 =>
                cases assump_28
                case inl assump_30 =>
                  cases assump_29
                  case intro assump_34 assump_35 =>
                    apply False.elim assump_34
                case inr assump_31 =>
                  cases assump_29
                  case intro assump_40 assump_41 =>
                    apply False.elim assump_40
          case inr assump_21 =>
            cases assump_21
            case inl assump_44 =>
              cases assump_44
              case inl assump_46 =>
                cases assump_19
                case intro assump_50 assump_51 =>
                  cases assump_51
                  case intro assump_54 assump_55 =>
                    cases assump_54
                    case inl assump_56 =>
                      cases assump_55
                      case intro assump_60 assump_61 =>
                        apply False.elim assump_60
                    case inr assump_57 =>
                      cases assump_55
                      case intro assump_66 assump_67 =>
                        apply False.elim assump_66
              case inr assump_47 =>
                cases assump_19
                case intro assump_72 assump_73 =>
                  cases assump_73
                  case intro assump_76 assump_77 =>
                    cases assump_76
                    case inl assump_78 =>
                      cases assump_77
                      case intro assump_82 assump_83 =>
                        apply False.elim assump_82
                    case inr assump_79 =>
                      cases assump_77
                      case intro assump_88 assump_89 =>
                        apply False.elim assump_88
            case inr assump_45 =>
              cases assump_19
              case intro assump_94 assump_95 =>
                cases assump_95
                case intro assump_98 assump_99 =>
                  cases assump_98
                  case inl assump_100 =>
                    cases assump_99
                    case intro assump_104 assump_105 =>
                      apply False.elim assump_104
                  case inr assump_101 =>
                    cases assump_99
                    case intro assump_110 assump_111 =>
                      apply False.elim assump_110
  case inr assump_7 =>
    cases assump_7
    case inl assump_114 =>
      cases assump_114
      case intro assump_116 assump_117 =>
        cases assump_1
        case intro assump_122 assump_123 =>
          cases assump_122
          case inl assump_124 =>
            cases assump_123
            case intro assump_128 assump_129 =>
              cases assump_129
              case intro assump_132 assump_133 =>
                cases assump_132
                case inl assump_134 =>
                  cases assump_133
                  case intro assump_138 assump_139 =>
                    apply False.elim assump_138
                case inr assump_135 =>
                  cases assump_133
                  case intro assump_144 assump_145 =>
                    apply False.elim assump_144
          case inr assump_125 =>
            cases assump_125
            case inl assump_148 =>
              cases assump_148
              case inl assump_150 =>
                cases assump_123
                case intro assump_154 assump_155 =>
                  cases assump_155
                  case intro assump_158 assump_159 =>
                    cases assump_158
                    case inl assump_160 =>
                      cases assump_159
                      case intro assump_164 assump_165 =>
                        apply False.elim assump_164
                    case inr assump_161 =>
                      cases assump_159
                      case intro assump_170 assump_171 =>
                        apply False.elim assump_170
              case inr assump_151 =>
                cases assump_123
                case intro assump_176 assump_177 =>
                  cases assump_177
                  case intro assump_180 assump_181 =>
                    cases assump_180
                    case inl assump_182 =>
                      cases assump_181
                      case intro assump_186 assump_187 =>
                        apply False.elim assump_186
                    case inr assump_183 =>
                      cases assump_181
                      case intro assump_192 assump_193 =>
                        apply False.elim assump_192
            case inr assump_149 =>
              cases assump_123
              case intro assump_198 assump_199 =>
                cases assump_199
                case intro assump_202 assump_203 =>
                  cases assump_202
                  case inl assump_204 =>
                    cases assump_203
                    case intro assump_208 assump_209 =>
                      apply False.elim assump_208
                  case inr assump_205 =>
                    cases assump_203
                    case intro assump_214 assump_215 =>
                      apply False.elim assump_214
    case inr assump_115 =>
      cases assump_115
      case inl assump_218 =>
        cases assump_1
        case intro assump_222 assump_223 =>
          cases assump_222
          case inl assump_224 =>
            cases assump_223
            case intro assump_228 assump_229 =>
              cases assump_229
              case intro assump_232 assump_233 =>
                cases assump_232
                case inl assump_234 =>
                  cases assump_233
                  case intro assump_238 assump_239 =>
                    apply False.elim assump_238
                case inr assump_235 =>
                  cases assump_233
                  case intro assump_244 assump_245 =>
                    apply False.elim assump_244
          case inr assump_225 =>
            cases assump_225
            case inl assump_248 =>
              cases assump_248
              case inl assump_250 =>
                cases assump_223
                case intro assump_254 assump_255 =>
                  cases assump_255
                  case intro assump_258 assump_259 =>
                    cases assump_258
                    case inl assump_260 =>
                      cases assump_259
                      case intro assump_264 assump_265 =>
                        apply False.elim assump_264
                    case inr assump_261 =>
                      cases assump_259
                      case intro assump_270 assump_271 =>
                        apply False.elim assump_270
              case inr assump_251 =>
                cases assump_223
                case intro assump_276 assump_277 =>
                  cases assump_277
                  case intro assump_280 assump_281 =>
                    cases assump_280
                    case inl assump_282 =>
                      cases assump_281
                      case intro assump_286 assump_287 =>
                        apply False.elim assump_286
                    case inr assump_283 =>
                      cases assump_281
                      case intro assump_292 assump_293 =>
                        apply False.elim assump_292
            case inr assump_249 =>
              cases assump_223
              case intro assump_298 assump_299 =>
                cases assump_299
                case intro assump_302 assump_303 =>
                  cases assump_302
                  case inl assump_304 =>
                    cases assump_303
                    case intro assump_308 assump_309 =>
                      apply False.elim assump_308
                  case inr assump_305 =>
                    cases assump_303
                    case intro assump_314 assump_315 =>
                      apply False.elim assump_314
      case inr assump_219 =>
        apply False.elim assump_219


variable (p7 p2 p3 p1 p4 : Prop)
theorem file40_82751 : ((((((True ∨ False) ∨ (p2 → p4)) → False) → (((p1 ∧ False) → False) ∧ ((p7 ∧ p1) ∧ (p3 → False)))) → False) → False) := by
  intro assump_5
  have assump_41 : ((((True ∨ False) ∨ (p2 → p4)) → False) → (((p1 ∧ False) → False) ∧ ((p7 ∧ p1) ∧ (p3 → False)))) := by
    intro assump_9
    apply And.intro
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      apply False.elim assump_12
    apply And.intro
    apply And.intro
    have assump_42 : ((True ∨ False) ∨ (p2 → p4)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_19 := assump_9 assump_42
    apply False.elim assump_19
    have assump_43 : ((True ∨ False) ∨ (p2 → p4)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_25 := assump_9 assump_43
    apply False.elim assump_25
    intro assump_29
    have assump_44 : ((True ∨ False) ∨ (p2 → p4)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_34 := assump_9 assump_44
    apply False.elim assump_34
  let assump_8 := assump_5 assump_41
  apply False.elim assump_8


variable (p5 p3 : Prop)
theorem file40_83900 : ((((((p5 ∧ p5) ∨ (p3 → p3)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p5 ∧ p5) ∨ (p3 → p3)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p5 ∧ p5) ∨ (p3 → p3)) := by
      apply Or.inr
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p5 p6 p1 p7 p3 p2 p0 : Prop)
theorem file40_84387 : (((((False → False) → False) → False) ∧ (((p4 → p6) → (p0 ∧ p6)) ∧ ((p7 → False) ∨ (False ∨ p1)))) → ((((False → False) → (False → False)) ∨ ((p0 ∧ p3) ∨ (p5 ∧ p7))) ∨ (((p2 → False) ∨ (True → False)) ∨ ((p5 ∧ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inl
        apply Or.inl
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      case inr assump_11 =>
        cases assump_11
        case inl assump_18 =>
          apply False.elim assump_18
        case inr assump_19 =>
          apply Or.inl
          apply Or.inl
          intro assump_24
          intro assump_25
          apply False.elim assump_25


variable (p0 p4 p2 p6 : Prop)
theorem file40_85254 : (((((p6 ∨ p0) ∧ (p2 ∨ True)) → ((True ∨ p6) ∨ (p4 ∨ p2))) → (((True ∨ False) → False) ∨ ((False → p6) → False))) → False) := by
  intro assump_1
  have assump_44 : (((p6 ∨ p0) ∧ (p2 ∨ True)) → ((True ∨ p6) ∨ (p4 ∨ p2))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case inl assump_12 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_9 =>
        cases assump_7
        case inl assump_20 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_21 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
  let assump_4 := assump_1 assump_44
  cases assump_4
  case inl assump_27 =>
    have assump_45 : (True ∨ False) := by
      apply Or.inl
      apply True.intro
    let assump_31 := assump_27 assump_45
    apply False.elim assump_31
  case inr assump_28 =>
    have assump_46 : (False → p6) := by
      intro assump_38
      apply False.elim assump_38
    let assump_37 := assump_28 assump_46
    apply False.elim assump_37


variable (p7 p0 p6 p5 p3 : Prop)
theorem file40_86569 : (((((p6 → False) ∨ (p7 ∨ p6)) ∧ ((p0 → False) ∧ (p5 ∧ True))) ∧ (((False → False) ∨ (p3 ∧ p3)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            have assump_73 : ((False → False) ∨ (p3 ∧ p3)) := by
              apply Or.inl
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_3 assump_73
            apply False.elim assump_22
      case inr assump_7 =>
        cases assump_7
        case inl assump_29 =>
          cases assump_5
          case intro assump_33 assump_34 =>
            cases assump_34
            case intro assump_37 assump_38 =>
              have assump_74 : ((False → False) ∨ (p3 ∧ p3)) := by
                apply Or.inl
                intro assump_46
                apply False.elim assump_46
              let assump_45 := assump_3 assump_74
              apply False.elim assump_45
        case inr assump_30 =>
          cases assump_5
          case intro assump_54 assump_55 =>
            cases assump_55
            case intro assump_58 assump_59 =>
              have assump_75 : ((False → False) ∨ (p3 ∧ p3)) := by
                apply Or.inl
                intro assump_67
                apply False.elim assump_67
              let assump_66 := assump_3 assump_75
              apply False.elim assump_66


variable (p2 p1 p3 p0 : Prop)
theorem file40_88219 : (((((p2 ∨ p3) ∧ (False ∧ p0)) → ((p2 ∨ p1) ∧ (False → p3))) → False) → False) := by
  intro assump_1
  have assump_28 : (((p2 ∨ p3) ∧ (False ∧ p0)) → ((p2 ∨ p1) ∧ (False → p3))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
      case inr assump_9 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
    intro assump_22
    apply False.elim assump_22
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p2 p5 p3 p7 p6 p0 p4 p1 : Prop)
theorem file40_88958 : ((((((True → p3) → (p5 ∨ p3)) ∨ ((p5 → False) ∧ (p7 ∧ p7))) → False) ∧ ((((p5 → p0) → (p2 ∧ p1)) ∨ ((False → p7) ∨ (True ∧ p4))) ∧ (((p6 ∨ p3) ∨ (False → p4)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_49 : ((p6 ∨ p3) ∨ (False → p4)) := by
          apply Or.inr
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_49
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_21 =>
          have assump_50 : ((p6 ∨ p3) ∨ (False → p4)) := by
            apply Or.inr
            intro assump_28
            apply False.elim assump_28
          let assump_27 := assump_7 assump_50
          apply False.elim assump_27
        case inr assump_22 =>
          cases assump_22
          case intro assump_34 assump_35 =>
            have assump_51 : ((p6 ∨ p3) ∨ (False → p4)) := by
              apply Or.inr
              intro assump_43
              apply False.elim assump_43
            let assump_42 := assump_7 assump_51
            apply False.elim assump_42


variable (p6 p0 : Prop)
theorem file40_90247 : ((((((p0 ∧ False) ∨ (p6 ∨ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p0 ∧ False) ∨ (p6 ∨ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((p0 ∧ False) ∨ (p6 ∨ True)) := by
      apply Or.inr
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p3 p2 p0 p1 p5 p4 : Prop)
theorem file40_90746 : (((((True ∨ p0) ∨ (False ∨ p1)) ∨ ((p0 → True) → False)) → (((p5 → p4) → (p7 ∨ p1)) → ((p1 ∧ p2) → (p3 ∨ True)))) ∨ ((((True ∧ p2) → False) → ((p5 ∨ p3) → (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case inl assump_12 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_14
        case inl assump_16 =>
          apply Or.inr
          apply True.intro
        case inr assump_17 =>
          apply Or.inr
          apply True.intro
      case inr assump_15 =>
        cases assump_15
        case inl assump_22 =>
          apply False.elim assump_22
        case inr assump_23 =>
          apply Or.inr
          apply True.intro
    case inr assump_13 =>
      apply Or.inr
      apply True.intro


variable (p2 p0 p5 p7 p3 p4 p6 p1 : Prop)
theorem file40_91661 : (((((p3 → p0) ∧ (p5 ∧ False)) → ((p7 ∧ p7) ∨ (p2 → p5))) ∨ (((False → False) ∧ (p7 → False)) ∨ ((p2 → p2) → (p7 → False)))) ∨ ((((p3 ∧ p6) ∧ (p5 ∨ p3)) ∨ ((p5 ∨ p7) → (p4 → False))) ∨ (((p7 ∨ p2) → False) → ((p6 → p1) ∧ (p6 ∨ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p7 p4 p0 p1 p2 p3 p6 p5 : Prop)
theorem file40_92152 : (((((p5 → False) → (p3 → False)) → ((p3 → False) ∨ (p6 → False))) → (((p1 ∨ p5) ∨ (False ∧ False)) ∧ ((p7 ∧ p2) → False))) → ((((p2 → p1) → False) ∨ ((p4 ∧ p2) → False)) → (((p2 → True) ∨ (p0 → False)) ∨ ((False → False) ∧ (p4 ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    apply Or.inl
    intro assump_9
    apply True.intro
  case inr assump_4 =>
    apply Or.inl
    apply Or.inl
    intro assump_14
    apply True.intro


variable (p7 p3 p2 p4 p1 p0 p5 p6 : Prop)
theorem file40_92709 : (((((p3 → False) ∨ (p6 ∨ p2)) ∧ ((p4 ∨ p6) → (p6 → p5))) ∨ (((p0 → True) → (False ∨ False)) ∧ ((p6 → False) → (p5 → p7)))) → ((((p7 ∧ p5) ∨ (p4 → False)) ∨ ((False → p4) → (p5 → p4))) → (((p6 ∧ True) ∨ (False → False)) ∨ ((p7 → False) ∨ (p1 ∧ p6))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        cases assump_1
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_15
            case inl assump_17 =>
              apply Or.inl
              apply Or.inr
              intro assump_23
              apply False.elim assump_23
            case inr assump_18 =>
              cases assump_18
              case inl assump_26 =>
                apply Or.inl
                apply Or.inl
                apply And.intro
                exact assump_26
                apply True.intro
              case inr assump_27 =>
                apply Or.inl
                apply Or.inr
                intro assump_36
                apply False.elim assump_36
        case inr assump_14 =>
          cases assump_14
          case intro assump_39 assump_40 =>
            apply Or.inl
            apply Or.inr
            intro assump_45
            apply False.elim assump_45
    case inr assump_6 =>
      cases assump_1
      case inl assump_50 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_52
          case inl assump_54 =>
            apply Or.inl
            apply Or.inr
            intro assump_60
            apply False.elim assump_60
          case inr assump_55 =>
            cases assump_55
            case inl assump_63 =>
              apply Or.inl
              apply Or.inl
              apply And.intro
              exact assump_63
              apply True.intro
            case inr assump_64 =>
              apply Or.inl
              apply Or.inr
              intro assump_73
              apply False.elim assump_73
      case inr assump_51 =>
        cases assump_51
        case intro assump_76 assump_77 =>
          apply Or.inl
          apply Or.inr
          intro assump_82
          apply False.elim assump_82
  case inr assump_4 =>
    cases assump_1
    case inl assump_87 =>
      cases assump_87
      case intro assump_89 assump_90 =>
        cases assump_89
        case inl assump_91 =>
          apply Or.inl
          apply Or.inr
          intro assump_97
          apply False.elim assump_97
        case inr assump_92 =>
          cases assump_92
          case inl assump_100 =>
            apply Or.inl
            apply Or.inl
            apply And.intro
            exact assump_100
            apply True.intro
          case inr assump_101 =>
            apply Or.inl
            apply Or.inr
            intro assump_110
            apply False.elim assump_110
    case inr assump_88 =>
      cases assump_88
      case intro assump_113 assump_114 =>
        apply Or.inl
        apply Or.inr
        intro assump_119
        apply False.elim assump_119


variable (p1 p3 p0 p7 p4 p6 p2 : Prop)
theorem file40_95936 : (((((p2 ∨ True) → False) → ((p2 ∧ p6) ∧ (p0 ∨ p0))) → (((p4 ∧ p1) → False) → ((False ∧ p2) → False))) ∨ ((((True → False) → (p1 ∨ p2)) ∨ ((p3 → p7) → (p0 → False))) → (((p4 ∨ p6) → False) → False))) := by
  apply Or.inl
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p2 p1 p0 p5 p7 : Prop)
theorem file40_96345 : ((((((p5 → False) ∨ (p2 ∧ p2)) ∧ ((False → False) → (p1 → p0))) → False) ∧ ((((p0 → False) → (p0 ∧ False)) → False) ∧ (((p1 → False) ∧ (False → False)) ∧ ((True ∧ p0) ∧ (p7 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              have assump_45 : ((p0 → False) → (p0 ∧ False)) := by
                intro assump_33
                apply And.intro
                exact assump_21
                have assump_46 : p0 := by
                  exact assump_21
                let assump_38 := assump_33 assump_46
                apply False.elim assump_38
              let assump_32 := assump_6 assump_45
              apply False.elim assump_32


variable (p4 p1 p5 p6 p2 p7 : Prop)
theorem file40_97426 : (((((p7 ∧ False) → False) ∨ ((True ∨ p4) → (p1 → True))) → False) → ((((True → False) ∧ (False ∨ p6)) ∨ ((p6 → p1) → (p2 ∧ p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        have assump_43 : (((p7 ∧ False) → False) ∨ ((True ∨ p4) → (p1 → True))) := by
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        let assump_17 := assump_1 assump_43
        apply False.elim assump_17
  case inr assump_4 =>
    have assump_44 : (((p7 ∧ False) → False) ∨ ((True ∨ p4) → (p1 → True))) := by
      apply Or.inl
      intro assump_33
      cases assump_33
      case intro assump_34 assump_35 =>
        apply False.elim assump_35
    let assump_32 := assump_1 assump_44
    apply False.elim assump_32


variable (p5 p6 p3 p4 p1 : Prop)
theorem file40_98504 : ((((((p4 ∨ p6) ∨ (False → False)) ∨ ((True ∨ p4) ∧ (p4 ∨ p5))) → (((p1 ∨ p3) ∧ (p3 ∨ False)) → ((False ∨ p3) ∨ (p4 ∧ p5)))) → False) → False) := by
  intro assump_1
  have assump_94 : ((((p4 ∨ p6) ∨ (False → False)) ∨ ((True ∨ p4) ∧ (p4 ∨ p5))) → (((p1 ∨ p3) ∧ (p3 ∨ False)) → ((False ∨ p3) ∨ (p4 ∧ p5)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case inl assump_13 =>
          cases assump_5
          case inl assump_17 =>
            cases assump_17
            case inl assump_19 =>
              cases assump_19
              case inl assump_21 =>
                apply Or.inl
                apply Or.inr
                exact assump_13
              case inr assump_22 =>
                apply Or.inl
                apply Or.inr
                exact assump_13
            case inr assump_20 =>
              apply Or.inl
              apply Or.inr
              exact assump_13
          case inr assump_18 =>
            cases assump_18
            case intro assump_29 assump_30 =>
              cases assump_29
              case inl assump_31 =>
                cases assump_30
                case inl assump_35 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_13
                case inr assump_36 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_13
              case inr assump_32 =>
                cases assump_30
                case inl assump_43 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_13
                case inr assump_44 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_13
        case inr assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case inl assump_53 =>
          cases assump_5
          case inl assump_57 =>
            cases assump_57
            case inl assump_59 =>
              cases assump_59
              case inl assump_61 =>
                apply Or.inl
                apply Or.inr
                exact assump_53
              case inr assump_62 =>
                apply Or.inl
                apply Or.inr
                exact assump_53
            case inr assump_60 =>
              apply Or.inl
              apply Or.inr
              exact assump_53
          case inr assump_58 =>
            cases assump_58
            case intro assump_69 assump_70 =>
              cases assump_69
              case inl assump_71 =>
                cases assump_70
                case inl assump_75 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_53
                case inr assump_76 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_53
              case inr assump_72 =>
                cases assump_70
                case inl assump_83 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_53
                case inr assump_84 =>
                  apply Or.inl
                  apply Or.inr
                  exact assump_53
        case inr assump_54 =>
          apply False.elim assump_54
  let assump_4 := assump_1 assump_94
  apply False.elim assump_4


variable (p4 p6 p5 p1 p3 p2 : Prop)
theorem file40_102004 : (((((p5 → p6) → False) ∧ ((True → False) ∨ (True ∧ False))) ∧ (((p4 → False) ∧ (p2 ∧ True)) ∧ ((p1 ∨ p3) → (p3 ∨ p4)))) → ((((p2 → False) ∨ (p5 ∨ p6)) ∨ ((p4 ∧ p5) ∧ (p6 ∧ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_12
          case inl assump_15 =>
            cases assump_10
            case intro assump_19 assump_20 =>
              cases assump_19
              case intro assump_21 assump_22 =>
                cases assump_22
                case intro assump_25 assump_26 =>
                  have assump_176 : True := by
                    apply True.intro
                  let assump_36 := assump_15 assump_176
                  apply False.elim assump_36
          case inr assump_16 =>
            cases assump_16
            case intro assump_40 assump_41 =>
              apply False.elim assump_41
    case inr assump_6 =>
      cases assump_6
      case inl assump_46 =>
        cases assump_1
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            cases assump_53
            case inl assump_56 =>
              cases assump_51
              case intro assump_60 assump_61 =>
                cases assump_60
                case intro assump_62 assump_63 =>
                  cases assump_63
                  case intro assump_66 assump_67 =>
                    have assump_177 : True := by
                      apply True.intro
                    let assump_77 := assump_56 assump_177
                    apply False.elim assump_77
            case inr assump_57 =>
              cases assump_57
              case intro assump_81 assump_82 =>
                apply False.elim assump_82
      case inr assump_47 =>
        cases assump_1
        case intro assump_89 assump_90 =>
          cases assump_89
          case intro assump_91 assump_92 =>
            cases assump_92
            case inl assump_95 =>
              cases assump_90
              case intro assump_99 assump_100 =>
                cases assump_99
                case intro assump_101 assump_102 =>
                  cases assump_102
                  case intro assump_105 assump_106 =>
                    have assump_178 : True := by
                      apply True.intro
                    let assump_116 := assump_95 assump_178
                    apply False.elim assump_116
            case inr assump_96 =>
              cases assump_96
              case intro assump_120 assump_121 =>
                apply False.elim assump_121
  case inr assump_4 =>
    cases assump_4
    case intro assump_126 assump_127 =>
      cases assump_126
      case intro assump_128 assump_129 =>
        cases assump_127
        case intro assump_134 assump_135 =>
          cases assump_1
          case intro assump_140 assump_141 =>
            cases assump_140
            case intro assump_142 assump_143 =>
              cases assump_143
              case inl assump_146 =>
                cases assump_141
                case intro assump_150 assump_151 =>
                  cases assump_150
                  case intro assump_152 assump_153 =>
                    cases assump_153
                    case intro assump_156 assump_157 =>
                      have assump_179 : p4 := by
                        exact assump_128
                      let assump_166 := assump_152 assump_179
                      apply False.elim assump_166
              case inr assump_147 =>
                cases assump_147
                case intro assump_170 assump_171 =>
                  apply False.elim assump_171


variable (p1 p5 p2 p6 p3 p0 : Prop)
theorem file40_105889 : (((((p6 → p2) ∧ (p0 ∧ False)) → False) ∨ (((p1 ∧ p0) → (p6 → False)) → False)) → ((((False → p2) → False) → False) ∨ (((p5 ∨ p3) ∧ (p3 ∧ p5)) ∧ ((True ∨ p3) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_28 : (False → p2) := by
      intro assump_10
      apply False.elim assump_10
    let assump_9 := assump_6 assump_28
    apply False.elim assump_9
  case inr assump_3 =>
    apply Or.inl
    intro assump_18
    have assump_29 : (False → p2) := by
      intro assump_22
      apply False.elim assump_22
    let assump_21 := assump_18 assump_29
    apply False.elim assump_21


variable (p3 p5 p7 p2 : Prop)
theorem file40_106602 : (((((p2 → False) ∧ (p7 → False)) → ((p5 ∧ p5) → False)) → (((False → False) ∨ (p2 → p3)) → False)) → ((((False ∨ p7) → False) ∧ ((p5 ∧ p2) ∨ (True ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_50 : (((p2 → False) ∧ (p7 → False)) → ((p5 ∧ p5) → False)) := by
          intro assump_18
          intro assump_19
          cases assump_19
          case intro assump_20 assump_21 =>
            cases assump_18
            case intro assump_26 assump_27 =>
              have assump_51 : p2 := by
                exact assump_10
              let assump_33 := assump_26 assump_51
              apply False.elim assump_33
        let assump_17 := assump_1 assump_50
        have assump_52 : ((False → False) ∨ (p2 → p3)) := by
          apply Or.inl
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_17 assump_52
        apply False.elim assump_37
    case inr assump_8 =>
      cases assump_8
      case intro assump_44 assump_45 =>
        apply False.elim assump_45


variable (p0 p2 p6 p3 p5 p7 p1 : Prop)
theorem file40_107865 : (((((p6 ∨ True) → False) → False) ∨ (((p7 ∨ p5) → (False ∨ p7)) → ((p1 ∧ p2) ∨ (p7 ∨ p0)))) ∨ ((((False → p3) → False) ∨ ((p1 ∨ p5) ∨ (p6 ∨ p6))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_8 : (p6 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p2 p4 p5 p3 p0 p7 p6 : Prop)
theorem file40_108275 : (((((p2 → p2) → (p4 → False)) ∧ ((p3 ∨ p6) → False)) ∧ (((p7 ∧ p6) → (p4 → p0)) ∧ ((p7 ∧ p5) ∧ (p2 ∧ p6)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              have assump_38 : (p3 ∨ p6) := by
                apply Or.inr
                exact assump_23
              let assump_34 := assump_5 assump_38
              apply False.elim assump_34


variable (p5 p1 p2 p0 p3 p4 p7 p6 : Prop)
theorem file40_109057 : ((((((False → p7) ∧ (p6 → p6)) → False) → False) → ((((p5 → p5) ∨ (p3 → p4)) → False) ∧ (((p3 → p0) → (p5 → False)) ∧ ((p5 ∧ p7) → (p1 ∧ p2))))) → False) := by
  intro assump_1
  have assump_26 : ((((False → p7) ∧ (p6 → p6)) → False) → False) := by
    intro assump_5
    have assump_27 : ((False → p7) ∧ (p6 → p6)) := by
      apply And.intro
      intro assump_9
      apply False.elim assump_9
      intro assump_12
      exact assump_12
    let assump_8 := assump_5 assump_27
    apply False.elim assump_8
  let assump_4 := assump_1 assump_26
  let assump_18 := And.left assump_4
  have assump_28 : ((p5 → p5) ∨ (p3 → p4)) := by
    apply Or.inl
    intro assump_20
    exact assump_20
  let assump_19 := assump_18 assump_28
  apply False.elim assump_19


variable (p0 p6 p5 p3 p4 p7 p2 : Prop)
theorem file40_109878 : ((((((p3 ∨ p4) ∨ (False → False)) → ((True → False) ∨ (p0 → p2))) → (((p3 → False) ∨ (False ∧ p6)) → ((p2 → p5) ∨ (p6 ∨ p6)))) ∧ ((((p3 ∧ False) ∧ (p7 ∨ p6)) → False) → False)) → False) := by
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    have assump_41 : (((p3 ∧ False) ∧ (p7 ∨ p6)) → False) := by
      intro assump_29
      cases assump_29
      case intro assump_30 assump_31 =>
        cases assump_30
        case intro assump_32 assump_33 =>
          apply False.elim assump_33
    let assump_28 := assump_23 assump_41
    apply False.elim assump_28


variable (p0 p1 p2 p5 p6 p3 p7 p4 : Prop)
theorem file40_110531 : ((((((True ∨ True) ∧ (p5 ∨ p6)) ∧ ((p7 → p4) → (p2 → p1))) ∧ (((False → p4) → False) ∧ ((p7 ∨ p1) → False))) ∧ ((((p3 → p7) ∨ (p3 → False)) ∨ ((p0 → False) ∧ (p0 → p5))) ∨ (((p4 ∨ p1) ∧ (p3 ∨ p6)) ∧ ((p5 → p0) ∧ (p3 → p5))))) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_27
          case inl assump_29 =>
            cases assump_28
            case inl assump_33 =>
              cases assump_24
              case intro assump_39 assump_40 =>
                cases assump_22
                case inl assump_45 =>
                  cases assump_45
                  case inl assump_47 =>
                    cases assump_47
                    case inl assump_49 =>
                      have assump_615 : (False → p4) := by
                        intro assump_56
                        apply False.elim assump_56
                      let assump_55 := assump_39 assump_615
                      apply False.elim assump_55
                    case inr assump_50 =>
                      have assump_616 : (False → p4) := by
                        intro assump_67
                        apply False.elim assump_67
                      let assump_66 := assump_39 assump_616
                      apply False.elim assump_66
                  case inr assump_48 =>
                    cases assump_48
                    case intro assump_73 assump_74 =>
                      have assump_617 : (False → p4) := by
                        intro assump_83
                        apply False.elim assump_83
                      let assump_82 := assump_39 assump_617
                      apply False.elim assump_82
                case inr assump_46 =>
                  cases assump_46
                  case intro assump_89 assump_90 =>
                    cases assump_89
                    case intro assump_91 assump_92 =>
                      cases assump_91
                      case inl assump_93 =>
                        cases assump_92
                        case inl assump_97 =>
                          cases assump_90
                          case intro assump_101 assump_102 =>
                            have assump_618 : (False → p4) := by
                              intro assump_115
                              apply False.elim assump_115
                            let assump_114 := assump_39 assump_618
                            apply False.elim assump_114
                        case inr assump_98 =>
                          cases assump_90
                          case intro assump_123 assump_124 =>
                            have assump_619 : (False → p4) := by
                              intro assump_136
                              apply False.elim assump_136
                            let assump_135 := assump_39 assump_619
                            apply False.elim assump_135
                      case inr assump_94 =>
                        cases assump_92
                        case inl assump_144 =>
                          cases assump_90
                          case intro assump_148 assump_149 =>
                            have assump_620 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_94
                            let assump_160 := assump_40 assump_620
                            apply False.elim assump_160
                        case inr assump_145 =>
                          cases assump_90
                          case intro assump_166 assump_167 =>
                            have assump_621 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_94
                            let assump_177 := assump_40 assump_621
                            apply False.elim assump_177
            case inr assump_34 =>
              cases assump_24
              case intro assump_185 assump_186 =>
                cases assump_22
                case inl assump_191 =>
                  cases assump_191
                  case inl assump_193 =>
                    cases assump_193
                    case inl assump_195 =>
                      have assump_622 : (False → p4) := by
                        intro assump_202
                        apply False.elim assump_202
                      let assump_201 := assump_185 assump_622
                      apply False.elim assump_201
                    case inr assump_196 =>
                      have assump_623 : (False → p4) := by
                        intro assump_213
                        apply False.elim assump_213
                      let assump_212 := assump_185 assump_623
                      apply False.elim assump_212
                  case inr assump_194 =>
                    cases assump_194
                    case intro assump_219 assump_220 =>
                      have assump_624 : (False → p4) := by
                        intro assump_229
                        apply False.elim assump_229
                      let assump_228 := assump_185 assump_624
                      apply False.elim assump_228
                case inr assump_192 =>
                  cases assump_192
                  case intro assump_235 assump_236 =>
                    cases assump_235
                    case intro assump_237 assump_238 =>
                      cases assump_237
                      case inl assump_239 =>
                        cases assump_238
                        case inl assump_243 =>
                          cases assump_236
                          case intro assump_247 assump_248 =>
                            have assump_625 : (False → p4) := by
                              intro assump_260
                              apply False.elim assump_260
                            let assump_259 := assump_185 assump_625
                            apply False.elim assump_259
                        case inr assump_244 =>
                          cases assump_236
                          case intro assump_268 assump_269 =>
                            have assump_626 : (False → p4) := by
                              intro assump_280
                              apply False.elim assump_280
                            let assump_279 := assump_185 assump_626
                            apply False.elim assump_279
                      case inr assump_240 =>
                        cases assump_238
                        case inl assump_288 =>
                          cases assump_236
                          case intro assump_292 assump_293 =>
                            have assump_627 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_240
                            let assump_303 := assump_186 assump_627
                            apply False.elim assump_303
                        case inr assump_289 =>
                          cases assump_236
                          case intro assump_309 assump_310 =>
                            have assump_628 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_240
                            let assump_319 := assump_186 assump_628
                            apply False.elim assump_319
          case inr assump_30 =>
            cases assump_28
            case inl assump_325 =>
              cases assump_24
              case intro assump_331 assump_332 =>
                cases assump_22
                case inl assump_337 =>
                  cases assump_337
                  case inl assump_339 =>
                    cases assump_339
                    case inl assump_341 =>
                      have assump_629 : (False → p4) := by
                        intro assump_348
                        apply False.elim assump_348
                      let assump_347 := assump_331 assump_629
                      apply False.elim assump_347
                    case inr assump_342 =>
                      have assump_630 : (False → p4) := by
                        intro assump_359
                        apply False.elim assump_359
                      let assump_358 := assump_331 assump_630
                      apply False.elim assump_358
                  case inr assump_340 =>
                    cases assump_340
                    case intro assump_365 assump_366 =>
                      have assump_631 : (False → p4) := by
                        intro assump_375
                        apply False.elim assump_375
                      let assump_374 := assump_331 assump_631
                      apply False.elim assump_374
                case inr assump_338 =>
                  cases assump_338
                  case intro assump_381 assump_382 =>
                    cases assump_381
                    case intro assump_383 assump_384 =>
                      cases assump_383
                      case inl assump_385 =>
                        cases assump_384
                        case inl assump_389 =>
                          cases assump_382
                          case intro assump_393 assump_394 =>
                            have assump_632 : (False → p4) := by
                              intro assump_407
                              apply False.elim assump_407
                            let assump_406 := assump_331 assump_632
                            apply False.elim assump_406
                        case inr assump_390 =>
                          cases assump_382
                          case intro assump_415 assump_416 =>
                            have assump_633 : (False → p4) := by
                              intro assump_428
                              apply False.elim assump_428
                            let assump_427 := assump_331 assump_633
                            apply False.elim assump_427
                      case inr assump_386 =>
                        cases assump_384
                        case inl assump_436 =>
                          cases assump_382
                          case intro assump_440 assump_441 =>
                            have assump_634 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_386
                            let assump_452 := assump_332 assump_634
                            apply False.elim assump_452
                        case inr assump_437 =>
                          cases assump_382
                          case intro assump_458 assump_459 =>
                            have assump_635 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_386
                            let assump_469 := assump_332 assump_635
                            apply False.elim assump_469
            case inr assump_326 =>
              cases assump_24
              case intro assump_477 assump_478 =>
                cases assump_22
                case inl assump_483 =>
                  cases assump_483
                  case inl assump_485 =>
                    cases assump_485
                    case inl assump_487 =>
                      have assump_636 : (False → p4) := by
                        intro assump_494
                        apply False.elim assump_494
                      let assump_493 := assump_477 assump_636
                      apply False.elim assump_493
                    case inr assump_488 =>
                      have assump_637 : (False → p4) := by
                        intro assump_505
                        apply False.elim assump_505
                      let assump_504 := assump_477 assump_637
                      apply False.elim assump_504
                  case inr assump_486 =>
                    cases assump_486
                    case intro assump_511 assump_512 =>
                      have assump_638 : (False → p4) := by
                        intro assump_521
                        apply False.elim assump_521
                      let assump_520 := assump_477 assump_638
                      apply False.elim assump_520
                case inr assump_484 =>
                  cases assump_484
                  case intro assump_527 assump_528 =>
                    cases assump_527
                    case intro assump_529 assump_530 =>
                      cases assump_529
                      case inl assump_531 =>
                        cases assump_530
                        case inl assump_535 =>
                          cases assump_528
                          case intro assump_539 assump_540 =>
                            have assump_639 : (False → p4) := by
                              intro assump_552
                              apply False.elim assump_552
                            let assump_551 := assump_477 assump_639
                            apply False.elim assump_551
                        case inr assump_536 =>
                          cases assump_528
                          case intro assump_560 assump_561 =>
                            have assump_640 : (False → p4) := by
                              intro assump_572
                              apply False.elim assump_572
                            let assump_571 := assump_477 assump_640
                            apply False.elim assump_571
                      case inr assump_532 =>
                        cases assump_530
                        case inl assump_580 =>
                          cases assump_528
                          case intro assump_584 assump_585 =>
                            have assump_641 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_532
                            let assump_595 := assump_478 assump_641
                            apply False.elim assump_595
                        case inr assump_581 =>
                          cases assump_528
                          case intro assump_601 assump_602 =>
                            have assump_642 : (p7 ∨ p1) := by
                              apply Or.inr
                              exact assump_532
                            let assump_611 := assump_478 assump_642
                            apply False.elim assump_611


variable (p0 p1 p4 p2 p6 p5 p3 : Prop)
theorem file40_125150 : ((((((p4 → p6) → (p6 → False)) ∨ ((p5 ∧ p6) ∧ (False ∧ False))) → False) ∧ ((((p3 → p1) → False) ∧ ((p2 → False) → (p1 → False))) ∧ (((p2 → False) ∧ (p5 ∧ p0)) ∧ ((p6 → p0) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              have assump_35 : (p6 → p0) := by
                intro assump_29
                exact assump_21
              let assump_28 := assump_15 assump_35
              apply False.elim assump_28


variable (p7 p1 p6 : Prop)
theorem file40_125995 : (((((p7 ∧ p1) → (True ∨ p6)) → False) → False) ∨ ((((True → False) → (p7 → False)) → False) → (((p7 ∧ p7) → False) → ((p6 ∧ False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_15 : ((p7 ∧ p1) → (True ∨ p6)) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p6 p3 p5 p1 : Prop)
theorem file40_126465 : ((((((p5 ∧ p5) ∨ (p3 ∨ p1)) ∧ ((p5 → True) ∧ (p0 ∨ p1))) ∨ (((p6 → True) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p5 ∧ p5) ∨ (p3 ∨ p1)) ∧ ((p5 → True) ∧ (p0 ∨ p1))) ∨ (((p6 → True) → False) → False)) := by
    apply Or.inr
    intro assump_5
    have assump_17 : (p6 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p3 p5 p4 : Prop)
theorem file40_127017 : (((((p5 → False) → False) → ((p4 ∨ p3) → (False → p5))) → False) → False) := by
  intro assump_16
  have assump_28 : (((p5 → False) → False) → ((p4 ∨ p3) → (False → p5))) := by
    intro assump_20
    intro assump_21
    intro assump_22
    apply False.elim assump_22
  let assump_19 := assump_16 assump_28
  apply False.elim assump_19


variable (p0 p7 p5 : Prop)
theorem file40_127404 : ((((((p0 → False) ∧ (p7 ∧ p5)) ∧ ((p5 → False) ∧ (p5 → False))) → False) → False) → False) := by
  intro assump_9
  have assump_39 : ((((p0 → False) ∧ (p7 ∧ p5)) ∧ ((p5 → False) ∧ (p5 → False))) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          cases assump_15
          case intro assump_26 assump_27 =>
            have assump_40 : p5 := by
              exact assump_21
            let assump_32 := assump_27 assump_40
            apply False.elim assump_32
  let assump_12 := assump_9 assump_39
  apply False.elim assump_12


variable (p7 p6 p0 p4 p3 p5 p2 : Prop)
theorem file40_128176 : (((((False → False) ∧ (False → p6)) → ((p7 → p7) → False)) → False) ∨ ((((p7 → False) → False) → ((True ∧ p2) ∧ (p4 ∨ p4))) ∧ (((p3 → p2) ∧ (p5 ∧ p0)) → ((p6 ∧ p4) → (p3 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_18 : ((False → False) ∧ (False → p6)) := by
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  have assump_19 : (p7 → p7) := by
    intro assump_12
    exact assump_12
  let assump_11 := assump_4 assump_19
  apply False.elim assump_11


variable (p1 p5 p2 p0 p3 p6 : Prop)
theorem file40_128812 : ((((((False ∨ p1) ∨ (True ∧ False)) ∨ ((p5 ∨ p6) ∨ (p2 → True))) ∨ (((p2 ∧ p0) ∨ (p3 ∧ p5)) → ((True ∧ p6) → False))) → False) → False) := by
  intro assump_34
  have assump_42 : ((((False ∨ p1) ∨ (True ∧ False)) ∨ ((p5 ∨ p6) ∨ (p2 → True))) ∨ (((p2 ∧ p0) ∨ (p3 ∧ p5)) → ((True ∧ p6) → False))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inr
    intro assump_38
    apply True.intro
  let assump_37 := assump_34 assump_42
  apply False.elim assump_37


variable (p4 p0 p7 : Prop)
theorem file40_129324 : ((((((False → p7) ∨ (p0 ∨ p4)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → p7) ∨ (p0 ∨ p4)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → p7) ∨ (p0 ∨ p4)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p6 : Prop)
theorem file40_129813 : ((((((p4 → True) → False) → False) ∧ (((p6 → True) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_24 : ((((p4 → True) → False) → False) ∧ (((p6 → True) → False) → False)) := by
    apply And.intro
    intro assump_5
    have assump_25 : (p4 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_25
    apply False.elim assump_8
    intro assump_13
    have assump_26 : (p6 → True) := by
      intro assump_17
      apply True.intro
    let assump_16 := assump_13 assump_26
    apply False.elim assump_16
  let assump_4 := assump_1 assump_24
  apply False.elim assump_4


variable (p7 p0 p4 p5 : Prop)
theorem file40_130503 : ((((((True → False) → False) ∨ ((p7 → False) → (p4 → p5))) ∨ (((p4 → p0) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True → False) → False) ∨ ((p7 → False) → (p4 → p5))) ∨ (((p4 → p0) → False) → False)) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p1 p0 p4 p5 p2 p7 : Prop)
theorem file40_131056 : (((((False ∨ p5) ∧ (p4 → False)) → ((p5 ∧ p0) ∧ (p2 ∧ True))) → (((p7 ∧ False) ∧ (False ∨ p4)) ∧ ((p0 → p5) → False))) → ((((p4 ∧ p4) ∧ (False → False)) ∨ ((p1 → p3) ∧ (p1 ∧ p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        have assump_123 : (((False ∨ p5) ∧ (p4 → False)) → ((p5 ∧ p0) ∧ (p2 ∧ True))) := by
          intro assump_18
          apply And.intro
          apply And.intro
          cases assump_18
          case intro assump_19 assump_20 =>
            cases assump_19
            case inl assump_21 =>
              apply False.elim assump_21
            case inr assump_22 =>
              exact assump_22
          cases assump_18
          case intro assump_29 assump_30 =>
            cases assump_29
            case inl assump_31 =>
              apply False.elim assump_31
            case inr assump_32 =>
              have assump_124 : p4 := by
                exact assump_8
              let assump_39 := assump_30 assump_124
              apply False.elim assump_39
          apply And.intro
          cases assump_18
          case intro assump_43 assump_44 =>
            cases assump_43
            case inl assump_45 =>
              apply False.elim assump_45
            case inr assump_46 =>
              have assump_125 : p4 := by
                exact assump_8
              let assump_53 := assump_44 assump_125
              apply False.elim assump_53
          apply True.intro
        let assump_17 := assump_1 assump_123
        let assump_57 := And.left assump_17
        let assump_58 := And.left assump_57
        let assump_59 := And.right assump_58
        apply False.elim assump_59
  case inr assump_4 =>
    cases assump_4
    case intro assump_64 assump_65 =>
      cases assump_65
      case intro assump_68 assump_69 =>
        have assump_126 : (((False ∨ p5) ∧ (p4 → False)) → ((p5 ∧ p0) ∧ (p2 ∧ True))) := by
          intro assump_77
          apply And.intro
          apply And.intro
          cases assump_77
          case intro assump_78 assump_79 =>
            cases assump_78
            case inl assump_80 =>
              apply False.elim assump_80
            case inr assump_81 =>
              exact assump_81
          cases assump_77
          case intro assump_88 assump_89 =>
            cases assump_88
            case inl assump_90 =>
              apply False.elim assump_90
            case inr assump_91 =>
              have assump_127 : p4 := by
                exact assump_69
              let assump_98 := assump_89 assump_127
              apply False.elim assump_98
          apply And.intro
          cases assump_77
          case intro assump_102 assump_103 =>
            cases assump_102
            case inl assump_104 =>
              apply False.elim assump_104
            case inr assump_105 =>
              have assump_128 : p4 := by
                exact assump_69
              let assump_112 := assump_103 assump_128
              apply False.elim assump_112
          apply True.intro
        let assump_76 := assump_1 assump_126
        let assump_116 := And.left assump_76
        let assump_117 := And.left assump_116
        let assump_118 := And.right assump_117
        apply False.elim assump_118


variable (p0 p7 p4 p3 p2 : Prop)
theorem file40_134490 : (((((True → False) → False) ∧ ((False ∧ p0) → False)) → False) → ((((p4 → False) ∧ (p3 ∧ False)) → ((p2 ∨ p7) ∧ (p3 ∨ p3))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_23 : (((True → False) → False) ∧ ((False ∧ p0) → False)) := by
    apply And.intro
    intro assump_8
    have assump_24 : True := by
      apply True.intro
    let assump_11 := assump_8 assump_24
    apply False.elim assump_11
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_16
  let assump_7 := assump_1 assump_23
  apply False.elim assump_7


variable (p7 p4 p5 p6 p0 : Prop)
theorem file40_135139 : ((((((False → False) → False) → False) → False) ∧ ((((False ∧ p7) → (p0 → False)) ∨ ((p4 → False) ∧ (p6 → p5))) → False)) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    have assump_33 : (((False ∧ p7) → (p0 → False)) ∨ ((p4 → False) ∧ (p6 → p5))) := by
      apply Or.inl
      intro assump_22
      intro assump_23
      cases assump_22
      case intro assump_26 assump_27 =>
        apply False.elim assump_26
    let assump_21 := assump_16 assump_33
    apply False.elim assump_21


