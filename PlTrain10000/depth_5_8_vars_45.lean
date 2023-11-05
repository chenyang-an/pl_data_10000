variable (p1 p0 p2 p5 p4 p6 p3 p7 : Prop)
theorem file45_50 : ((((((p6 → p3) → (p0 ∨ p6)) ∨ ((p4 → False) ∨ (p0 → False))) → (((p7 ∧ p4) ∧ (p1 → p5)) → ((p7 ∨ p3) ∨ (p6 → p2)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p6 → p3) → (p0 ∨ p6)) ∨ ((p4 → False) ∨ (p0 → False))) → (((p7 ∧ p4) ∧ (p1 → p5)) → ((p7 ∨ p3) ∨ (p6 → p2)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_5
        case inl assump_17 =>
          apply Or.inl
          apply Or.inl
          exact assump_9
        case inr assump_18 =>
          cases assump_18
          case inl assump_21 =>
            apply Or.inl
            apply Or.inl
            exact assump_9
          case inr assump_22 =>
            apply Or.inl
            apply Or.inl
            exact assump_9
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p7 p4 p3 p6 p0 p1 : Prop)
theorem file45_1022 : ((((((p7 ∧ p3) → (True ∨ p4)) ∨ ((p7 → False) → False)) → False) ∧ ((((p0 ∨ p6) ∨ (p7 ∨ p0)) ∧ ((p6 ∧ p1) → (False ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p7 ∧ p3) → (True ∨ p4)) ∨ ((p7 → False) → False)) := by
      apply Or.inl
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply True.intro
    let assump_9 := assump_2 assump_20
    apply False.elim assump_9


variable (p5 p2 p0 p6 p1 p4 p7 p3 : Prop)
theorem file45_1605 : ((((((p7 ∨ p6) ∧ (p4 → p4)) ∧ ((p3 → p3) ∧ (p4 ∨ p2))) → (((False ∧ p7) → False) → ((p7 → p6) → False))) ∧ ((((p5 ∧ p0) → (p4 → p5)) ∨ ((p4 → False) → False)) ∧ (((p6 → False) → False) ∧ ((True ∨ p1) ∧ (True → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_7
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              have assump_62 : True := by
                apply True.intro
              let assump_24 := assump_17 assump_62
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_63 : True := by
                apply True.intro
              let assump_32 := assump_17 assump_63
              apply False.elim assump_32
      case inr assump_9 =>
        cases assump_7
        case intro assump_38 assump_39 =>
          cases assump_39
          case intro assump_42 assump_43 =>
            cases assump_42
            case inl assump_44 =>
              have assump_64 : True := by
                apply True.intro
              let assump_50 := assump_43 assump_64
              apply False.elim assump_50
            case inr assump_45 =>
              have assump_65 : True := by
                apply True.intro
              let assump_58 := assump_43 assump_65
              apply False.elim assump_58


variable (p2 p3 p4 p0 p5 p6 p1 p7 : Prop)
theorem file45_3235 : ((((((p3 ∧ p1) → (p6 → p6)) ∨ ((False → p5) ∧ (p6 ∨ p6))) → False) ∨ ((((p6 ∧ p2) ∧ (False ∧ p7)) ∧ ((p0 → False) ∧ (False ∧ False))) ∧ (((p4 ∧ p1) ∨ (False ∨ p2)) → ((True ∧ p7) ∨ (True ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_36 : (((p3 ∧ p1) → (p6 → p6)) ∨ ((False → p5) ∧ (p6 ∨ p6))) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      cases assump_7
      case intro assump_11 assump_12 =>
        exact assump_8
    let assump_6 := assump_2 assump_36
    apply False.elim assump_6
  case inr assump_3 =>
    cases assump_3
    case intro assump_20 assump_21 =>
      cases assump_20
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_25
            case intro assump_32 assump_33 =>
              apply False.elim assump_32


variable (p1 p5 p0 p2 p3 p6 p4 p7 : Prop)
theorem file45_4262 : (((((True ∨ p7) → False) ∧ ((p7 → p7) → (False ∧ p2))) ∨ (((p4 → p7) ∧ (p6 ∧ p3)) ∧ ((p1 → p6) → False))) → ((((p1 ∨ p0) → (p3 → p7)) → ((p2 → p7) → (p5 ∨ False))) ∧ (((p2 ∧ p0) → False) ∧ ((p7 → False) ∨ (p3 ∨ p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      have assump_134 : (p7 → p7) := by
        intro assump_17
        exact assump_17
      let assump_16 := assump_11 assump_134
      let assump_20 := And.left assump_16
      apply False.elim assump_20
  case inr assump_9 =>
    cases assump_9
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          have assump_135 : (p1 → p6) := by
            intro assump_39
            exact assump_30
          let assump_38 := assump_25 assump_135
          apply False.elim assump_38
  apply And.intro
  intro assump_45
  cases assump_45
  case intro assump_46 assump_47 =>
    cases assump_1
    case inl assump_52 =>
      cases assump_52
      case intro assump_54 assump_55 =>
        have assump_136 : (p7 → p7) := by
          intro assump_61
          exact assump_61
        let assump_60 := assump_55 assump_136
        let assump_64 := And.left assump_60
        apply False.elim assump_64
    case inr assump_53 =>
      cases assump_53
      case intro assump_68 assump_69 =>
        cases assump_68
        case intro assump_70 assump_71 =>
          cases assump_71
          case intro assump_74 assump_75 =>
            have assump_137 : (p1 → p6) := by
              intro assump_83
              exact assump_74
            let assump_82 := assump_69 assump_137
            apply False.elim assump_82
  cases assump_1
  case inl assump_89 =>
    cases assump_89
    case intro assump_91 assump_92 =>
      apply Or.inl
      intro assump_97
      have assump_138 : (p7 → p7) := by
        intro assump_102
        exact assump_102
      let assump_101 := assump_92 assump_138
      let assump_105 := And.left assump_101
      apply False.elim assump_105
  case inr assump_90 =>
    cases assump_90
    case intro assump_109 assump_110 =>
      cases assump_109
      case intro assump_111 assump_112 =>
        cases assump_112
        case intro assump_115 assump_116 =>
          apply Or.inl
          intro assump_123
          have assump_139 : (p1 → p6) := by
            intro assump_128
            exact assump_115
          let assump_127 := assump_110 assump_139
          apply False.elim assump_127


variable (p0 p6 p5 : Prop)
theorem file45_6950 : (((((True → False) → False) ∨ ((p0 → p6) ∨ (p5 ∧ p6))) → False) → False) := by
  intro assump_8
  have assump_22 : (((True → False) → False) ∨ ((p0 → p6) ∨ (p5 ∧ p6))) := by
    apply Or.inl
    intro assump_12
    have assump_23 : True := by
      apply True.intro
    let assump_15 := assump_12 assump_23
    apply False.elim assump_15
  let assump_11 := assump_8 assump_22
  apply False.elim assump_11


variable (p5 p2 p7 p1 p3 p4 : Prop)
theorem file45_7415 : (((((True ∧ p1) → (p1 → True)) → ((True → p4) ∨ (p2 ∨ p2))) ∧ (((False → p1) → (p5 → p5)) → False)) → ((((p5 ∧ p1) → (p7 → p3)) → ((p2 → True) → False)) ∨ (((False ∧ p4) ∧ (p4 → False)) → False))) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply Or.inl
    intro assump_16
    intro assump_17
    have assump_34 : ((False → p1) → (p5 → p5)) := by
      intro assump_25
      intro assump_26
      exact assump_26
    let assump_24 := assump_11 assump_34
    apply False.elim assump_24


variable (p3 p0 p2 p4 p5 p6 p1 : Prop)
theorem file45_8000 : (((((p3 → True) → False) → ((True → False) → (p4 → p1))) → False) → ((((p3 ∧ p5) → (p3 → p2)) → ((False → p2) ∧ (p5 ∧ p6))) ∧ (((p0 → False) → False) ∨ ((False ∧ p6) → False)))) := by
  intro assump_21
  apply And.intro
  intro assump_22
  apply And.intro
  intro assump_23
  apply False.elim assump_23
  apply And.intro
  have assump_94 : (((p3 → True) → False) → ((True → False) → (p4 → p1))) := by
    intro assump_31
    intro assump_32
    intro assump_33
    have assump_95 : (p3 → True) := by
      intro assump_41
      apply True.intro
    let assump_40 := assump_31 assump_95
    apply False.elim assump_40
  let assump_30 := assump_21 assump_94
  apply False.elim assump_30
  have assump_96 : (((p3 → True) → False) → ((True → False) → (p4 → p1))) := by
    intro assump_53
    intro assump_54
    intro assump_55
    have assump_97 : (p3 → True) := by
      intro assump_63
      apply True.intro
    let assump_62 := assump_53 assump_97
    apply False.elim assump_62
  let assump_52 := assump_21 assump_96
  apply False.elim assump_52
  apply Or.inl
  intro assump_72
  have assump_98 : (((p3 → True) → False) → ((True → False) → (p4 → p1))) := by
    intro assump_77
    intro assump_78
    intro assump_79
    have assump_99 : (p3 → True) := by
      intro assump_87
      apply True.intro
    let assump_86 := assump_77 assump_99
    apply False.elim assump_86
  let assump_76 := assump_21 assump_98
  apply False.elim assump_76


variable (p2 p7 p6 p1 p4 p3 p0 : Prop)
theorem file45_9509 : (((((p4 → False) ∧ (False ∧ p7)) ∧ ((p6 → p2) → False)) → False) ∨ ((((p6 → p1) ∧ (p3 → False)) ∨ ((p6 → False) ∨ (p1 ∧ p2))) → (((p0 ∨ p3) ∧ (p4 → False)) ∨ ((p3 → False) ∧ (p7 → p2))))) := by
  apply Or.inl
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    cases assump_31
    case intro assump_33 assump_34 =>
      cases assump_34
      case intro assump_37 assump_38 =>
        apply False.elim assump_37


variable (p3 p0 p5 p1 p7 p4 : Prop)
theorem file45_10005 : ((((((p4 → False) → (p3 ∨ p0)) → ((False ∧ p1) → False)) → (((p7 ∨ p1) → False) → ((False ∧ p5) → (p7 → False)))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p4 → False) → (p3 ∨ p0)) → ((False ∧ p1) → False)) → (((p7 ∨ p1) → False) → ((False ∧ p5) → (p7 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p6 p7 p1 p4 p5 : Prop)
theorem file45_10588 : (((((True ∨ p4) ∨ (False → False)) ∨ ((False ∨ p3) ∨ (p6 ∧ p5))) ∨ (((False → p1) → False) → ((p7 ∨ True) → (p7 ∨ p1)))) ∨ ((((p1 ∨ False) → False) ∧ ((True → False) → (p5 ∧ p5))) ∧ (((False ∨ True) ∧ (p7 ∨ True)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p6 p2 p5 p3 : Prop)
theorem file45_10967 : (((((p3 → p3) ∧ (False ∧ p2)) → False) → False) → ((((True → False) → False) ∨ ((p6 → p5) ∨ (p3 → False))) ∧ (((False → False) ∨ (True → True)) → False))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_48 : True := by
    apply True.intro
  let assump_7 := assump_4 assump_48
  apply False.elim assump_7
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    have assump_49 : (((p3 → p3) ∧ (False ∧ p2)) → False) := by
      intro assump_19
      cases assump_19
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
    let assump_18 := assump_1 assump_49
    apply False.elim assump_18
  case inr assump_13 =>
    have assump_50 : (((p3 → p3) ∧ (False ∧ p2)) → False) := by
      intro assump_36
      cases assump_36
      case intro assump_37 assump_38 =>
        cases assump_38
        case intro assump_41 assump_42 =>
          apply False.elim assump_41
    let assump_35 := assump_1 assump_50
    apply False.elim assump_35


variable (p2 p5 p6 p1 p4 p7 : Prop)
theorem file45_12099 : (((((p6 ∨ p2) → (False ∨ p5)) ∧ ((p7 → p7) → (True ∧ True))) ∨ (((p7 ∨ False) → (p5 → p4)) → ((p6 → False) ∧ (p1 → p1)))) → ((((p6 ∨ p4) ∨ (False → False)) ∨ ((p1 → p5) → False)) ∨ (((p2 → p6) ∧ (False → False)) → False))) := by
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_14
      apply False.elim assump_14
  case inr assump_7 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_19
    apply False.elim assump_19


variable (p6 p1 p7 p0 p4 p5 p3 : Prop)
theorem file45_12740 : (((((False → p3) → False) → ((p3 → p3) ∨ (p0 → False))) → (((p3 → p7) → (False → False)) → False)) → ((((False ∨ False) → False) → ((p5 ∧ p4) ∧ (p6 ∧ True))) → (((False ∧ p7) → False) → ((p1 → False) → (True → p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  have assump_31 : (((False → p3) → False) → ((p3 → p3) ∨ (p0 → False))) := by
    intro assump_17
    apply Or.inl
    intro assump_20
    exact assump_20
  let assump_16 := assump_1 assump_31
  have assump_32 : ((p3 → p7) → (False → False)) := by
    intro assump_24
    intro assump_25
    apply False.elim assump_25
  let assump_23 := assump_16 assump_32
  apply False.elim assump_23


variable (p7 p3 p6 p1 p4 : Prop)
theorem file45_13494 : (((((True ∨ p1) → False) → False) ∧ (((p4 ∨ p6) → (p3 → p3)) → False)) → ((((p1 ∨ p1) ∨ (False → p3)) ∨ ((True ∧ True) ∧ (p7 → False))) ∧ (((p4 ∨ p1) → False) ∨ ((False → True) ∨ (p1 ∨ p6))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  cases assump_1
  case intro assump_11 assump_12 =>
    apply Or.inl
    intro assump_17
    cases assump_17
    case inl assump_18 =>
      have assump_54 : ((p4 ∨ p6) → (p3 → p3)) := by
        intro assump_24
        intro assump_25
        cases assump_24
        case inl assump_28 =>
          exact assump_25
        case inr assump_29 =>
          exact assump_25
      let assump_23 := assump_12 assump_54
      apply False.elim assump_23
    case inr assump_19 =>
      have assump_55 : ((p4 ∨ p6) → (p3 → p3)) := by
        intro assump_41
        intro assump_42
        cases assump_41
        case inl assump_45 =>
          exact assump_42
        case inr assump_46 =>
          exact assump_42
      let assump_40 := assump_12 assump_55
      apply False.elim assump_40


variable (p3 p2 p1 p6 p7 p5 p4 : Prop)
theorem file45_14713 : ((((((p2 → False) → (p3 ∧ p1)) ∨ ((True → p4) → (p6 → False))) ∧ (((p2 → False) → False) → False)) ∧ ((((True ∨ p7) → False) → ((p3 → False) ∧ (p5 → p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_66 : (((True ∨ p7) → False) → ((p3 → False) ∧ (p5 → p7))) := by
          intro assump_15
          apply And.intro
          intro assump_16
          have assump_67 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_21 := assump_15 assump_67
          apply False.elim assump_21
          intro assump_25
          have assump_68 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_30 := assump_15 assump_68
          apply False.elim assump_30
        let assump_14 := assump_3 assump_66
        apply False.elim assump_14
      case inr assump_7 =>
        have assump_69 : (((True ∨ p7) → False) → ((p3 → False) ∧ (p5 → p7))) := by
          intro assump_44
          apply And.intro
          intro assump_45
          have assump_70 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_50 := assump_44 assump_70
          apply False.elim assump_50
          intro assump_54
          have assump_71 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_59 := assump_44 assump_71
          apply False.elim assump_59
        let assump_43 := assump_3 assump_69
        apply False.elim assump_43


variable (p4 p3 p6 p5 p1 p7 p2 : Prop)
theorem file45_16420 : (((((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) → False) → ((((p6 ∨ p2) ∧ (True ∧ p4)) ∨ ((p7 → False) ∨ (p1 → False))) → (((p3 → False) ∧ (p7 → False)) ∧ ((p4 ∨ p4) ∧ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          have assump_454 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
            intro assump_23
            apply And.intro
            intro assump_24
            have assump_455 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_29 := assump_23 assump_455
            apply False.elim assump_29
            intro assump_33
            have assump_456 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_38 := assump_23 assump_456
            apply False.elim assump_38
          let assump_22 := assump_1 assump_454
          apply False.elim assump_22
      case inr assump_11 =>
        cases assump_9
        case intro assump_47 assump_48 =>
          have assump_457 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
            intro assump_56
            apply And.intro
            intro assump_57
            have assump_458 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_62 := assump_56 assump_458
            apply False.elim assump_62
            intro assump_66
            exact assump_11
          let assump_55 := assump_1 assump_457
          apply False.elim assump_55
  case inr assump_7 =>
    cases assump_7
    case inl assump_74 =>
      have assump_459 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_81
        apply And.intro
        intro assump_82
        have assump_460 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_87 := assump_81 assump_460
        apply False.elim assump_87
        intro assump_91
        have assump_461 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_96 := assump_81 assump_461
        apply False.elim assump_96
      let assump_80 := assump_1 assump_459
      apply False.elim assump_80
    case inr assump_75 =>
      have assump_462 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_108
        apply And.intro
        intro assump_109
        have assump_463 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_114 := assump_108 assump_463
        apply False.elim assump_114
        intro assump_118
        have assump_464 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_123 := assump_108 assump_464
        apply False.elim assump_123
      let assump_107 := assump_1 assump_462
      apply False.elim assump_107
  intro assump_130
  cases assump_2
  case inl assump_133 =>
    cases assump_133
    case intro assump_135 assump_136 =>
      cases assump_135
      case inl assump_137 =>
        cases assump_136
        case intro assump_141 assump_142 =>
          have assump_465 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
            intro assump_150
            apply And.intro
            intro assump_151
            have assump_466 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_156 := assump_150 assump_466
            apply False.elim assump_156
            intro assump_160
            have assump_467 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_165 := assump_150 assump_467
            apply False.elim assump_165
          let assump_149 := assump_1 assump_465
          apply False.elim assump_149
      case inr assump_138 =>
        cases assump_136
        case intro assump_174 assump_175 =>
          have assump_468 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
            intro assump_183
            apply And.intro
            intro assump_184
            have assump_469 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_189 := assump_183 assump_469
            apply False.elim assump_189
            intro assump_193
            exact assump_138
          let assump_182 := assump_1 assump_468
          apply False.elim assump_182
  case inr assump_134 =>
    cases assump_134
    case inl assump_201 =>
      have assump_470 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_208
        apply And.intro
        intro assump_209
        have assump_471 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_214 := assump_208 assump_471
        apply False.elim assump_214
        intro assump_218
        have assump_472 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_223 := assump_208 assump_472
        apply False.elim assump_223
      let assump_207 := assump_1 assump_470
      apply False.elim assump_207
    case inr assump_202 =>
      have assump_473 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_235
        apply And.intro
        intro assump_236
        have assump_474 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_241 := assump_235 assump_474
        apply False.elim assump_241
        intro assump_245
        have assump_475 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_250 := assump_235 assump_475
        apply False.elim assump_250
      let assump_234 := assump_1 assump_473
      apply False.elim assump_234
  apply And.intro
  cases assump_2
  case inl assump_257 =>
    cases assump_257
    case intro assump_259 assump_260 =>
      cases assump_259
      case inl assump_261 =>
        cases assump_260
        case intro assump_265 assump_266 =>
          apply Or.inl
          exact assump_266
      case inr assump_262 =>
        cases assump_260
        case intro assump_275 assump_276 =>
          apply Or.inl
          exact assump_276
  case inr assump_258 =>
    cases assump_258
    case inl assump_283 =>
      have assump_476 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_290
        apply And.intro
        intro assump_291
        have assump_477 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_296 := assump_290 assump_477
        apply False.elim assump_296
        intro assump_300
        have assump_478 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_305 := assump_290 assump_478
        apply False.elim assump_305
      let assump_289 := assump_1 assump_476
      apply False.elim assump_289
    case inr assump_284 =>
      have assump_479 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_317
        apply And.intro
        intro assump_318
        have assump_480 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_323 := assump_317 assump_480
        apply False.elim assump_323
        intro assump_327
        have assump_481 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_332 := assump_317 assump_481
        apply False.elim assump_332
      let assump_316 := assump_1 assump_479
      apply False.elim assump_316
  intro assump_339
  cases assump_2
  case inl assump_342 =>
    cases assump_342
    case intro assump_344 assump_345 =>
      cases assump_344
      case inl assump_346 =>
        cases assump_345
        case intro assump_350 assump_351 =>
          have assump_482 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
            intro assump_359
            apply And.intro
            intro assump_360
            have assump_483 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_365 := assump_359 assump_483
            apply False.elim assump_365
            intro assump_369
            exact assump_339
          let assump_358 := assump_1 assump_482
          apply False.elim assump_358
      case inr assump_347 =>
        cases assump_345
        case intro assump_379 assump_380 =>
          have assump_484 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
            intro assump_388
            apply And.intro
            intro assump_389
            have assump_485 : (True ∨ p5) := by
              apply Or.inl
              apply True.intro
            let assump_394 := assump_388 assump_485
            apply False.elim assump_394
            intro assump_398
            exact assump_347
          let assump_387 := assump_1 assump_484
          apply False.elim assump_387
  case inr assump_343 =>
    cases assump_343
    case inl assump_406 =>
      have assump_486 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_413
        apply And.intro
        intro assump_414
        have assump_487 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_419 := assump_413 assump_487
        apply False.elim assump_419
        intro assump_423
        exact assump_339
      let assump_412 := assump_1 assump_486
      apply False.elim assump_412
    case inr assump_407 =>
      have assump_488 : (((True ∨ p5) → False) → ((True → False) ∧ (p4 → p2))) := by
        intro assump_436
        apply And.intro
        intro assump_437
        have assump_489 : (True ∨ p5) := by
          apply Or.inl
          apply True.intro
        let assump_442 := assump_436 assump_489
        apply False.elim assump_442
        intro assump_446
        exact assump_339
      let assump_435 := assump_1 assump_488
      apply False.elim assump_435


variable (p7 p6 p1 p3 p0 p2 : Prop)
theorem file45_26632 : (((((p2 → False) → (p3 ∧ p7)) ∧ ((True → False) ∧ (p6 ∨ p2))) → False) ∨ ((((p6 ∨ p3) → (p1 → False)) ∧ ((p3 → False) → (p2 → False))) → (((False → False) → (p0 → p7)) ∧ ((p0 → False) → False)))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_11
      case inl assump_14 =>
        have assump_30 : True := by
          apply True.intro
        let assump_19 := assump_10 assump_30
        apply False.elim assump_19
      case inr assump_15 =>
        have assump_31 : True := by
          apply True.intro
        let assump_26 := assump_10 assump_31
        apply False.elim assump_26


variable (p6 p1 p3 p2 p0 p7 p4 : Prop)
theorem file45_27401 : (((((p1 → False) ∨ (False ∧ p4)) ∨ ((p0 ∨ p4) ∧ (p7 → False))) → (((p2 ∧ False) → (p2 → False)) → ((p1 ∨ True) ∨ (p2 ∧ p3)))) ∨ ((((p1 ∧ p2) ∨ (p4 ∧ p0)) → False) ∧ (((p2 → p3) → False) → ((p2 → False) → (p6 ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
  case inr assump_6 =>
    cases assump_6
    case intro assump_15 assump_16 =>
      cases assump_15
      case inl assump_17 =>
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_18 =>
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p5 p0 p4 p6 : Prop)
theorem file45_28289 : (((((False → False) → False) → False) → False) → ((((p5 → False) → (p0 ∨ False)) ∨ ((p6 → False) ∧ (p0 ∨ p4))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_65 : (((False → False) → False) → False) := by
      intro assump_10
      have assump_66 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_10 assump_66
      apply False.elim assump_13
    let assump_9 := assump_1 assump_65
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case intro assump_23 assump_24 =>
      cases assump_24
      case inl assump_27 =>
        have assump_67 : (((False → False) → False) → False) := by
          intro assump_34
          have assump_68 : (False → False) := by
            intro assump_38
            apply False.elim assump_38
          let assump_37 := assump_34 assump_68
          apply False.elim assump_37
        let assump_33 := assump_1 assump_67
        apply False.elim assump_33
      case inr assump_28 =>
        have assump_69 : (((False → False) → False) → False) := by
          intro assump_52
          have assump_70 : (False → False) := by
            intro assump_56
            apply False.elim assump_56
          let assump_55 := assump_52 assump_70
          apply False.elim assump_55
        let assump_51 := assump_1 assump_69
        apply False.elim assump_51


variable (p5 p4 p1 : Prop)
theorem file45_29777 : (((((p1 ∨ p1) ∧ (p4 ∧ p1)) ∨ ((True → False) → (True → p5))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p1 ∨ p1) ∧ (p4 ∧ p1)) ∨ ((True → False) → (True → p5))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p0 : Prop)
theorem file45_30257 : (((((False ∧ p4) → False) ∧ ((False ∧ p0) → (False ∨ False))) → False) → ((((True ∧ True) → (True → False)) → False) → (((p0 ∨ p4) ∧ (True ∨ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case inl assump_10 =>
        have assump_96 : (((False ∧ p4) → False) ∧ ((False ∧ p0) → (False ∨ False))) := by
          apply And.intro
          intro assump_19
          cases assump_19
          case intro assump_20 assump_21 =>
            apply False.elim assump_20
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            apply False.elim assump_25
        let assump_18 := assump_1 assump_96
        apply False.elim assump_18
      case inr assump_11 =>
        have assump_97 : (((False ∧ p4) → False) ∧ ((False ∧ p0) → (False ∨ False))) := by
          apply And.intro
          intro assump_39
          cases assump_39
          case intro assump_40 assump_41 =>
            apply False.elim assump_40
          intro assump_44
          cases assump_44
          case intro assump_45 assump_46 =>
            apply False.elim assump_45
        let assump_38 := assump_1 assump_97
        apply False.elim assump_38
    case inr assump_7 =>
      cases assump_5
      case inl assump_54 =>
        have assump_98 : (((False ∧ p4) → False) ∧ ((False ∧ p0) → (False ∨ False))) := by
          apply And.intro
          intro assump_63
          cases assump_63
          case intro assump_64 assump_65 =>
            apply False.elim assump_64
          intro assump_68
          cases assump_68
          case intro assump_69 assump_70 =>
            apply False.elim assump_69
        let assump_62 := assump_1 assump_98
        apply False.elim assump_62
      case inr assump_55 =>
        have assump_99 : (((False ∧ p4) → False) ∧ ((False ∧ p0) → (False ∨ False))) := by
          apply And.intro
          intro assump_83
          cases assump_83
          case intro assump_84 assump_85 =>
            apply False.elim assump_84
          intro assump_88
          cases assump_88
          case intro assump_89 assump_90 =>
            apply False.elim assump_89
        let assump_82 := assump_1 assump_99
        apply False.elim assump_82


variable (p5 p2 p1 p7 p3 p4 p0 p6 : Prop)
theorem file45_32677 : ((((((p1 → False) ∧ (p7 ∨ p0)) ∨ ((p6 → p1) ∨ (p2 ∧ p3))) ∧ (((p4 → p5) → (p1 ∨ True)) → False)) ∧ ((((p2 ∧ p2) ∧ (p2 → False)) ∧ ((False ∧ p7) ∧ (p4 ∧ p1))) ∧ (((True → p4) → (True ∨ False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case inl assump_12 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    cases assump_21
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case intro assump_34 assump_35 =>
                        apply False.elim assump_34
          case inr assump_13 =>
            cases assump_3
            case intro assump_42 assump_43 =>
              cases assump_42
              case intro assump_44 assump_45 =>
                cases assump_44
                case intro assump_46 assump_47 =>
                  cases assump_46
                  case intro assump_48 assump_49 =>
                    cases assump_45
                    case intro assump_56 assump_57 =>
                      cases assump_56
                      case intro assump_58 assump_59 =>
                        apply False.elim assump_58
      case inr assump_7 =>
        cases assump_7
        case inl assump_62 =>
          cases assump_3
          case intro assump_68 assump_69 =>
            cases assump_68
            case intro assump_70 assump_71 =>
              cases assump_70
              case intro assump_72 assump_73 =>
                cases assump_72
                case intro assump_74 assump_75 =>
                  cases assump_71
                  case intro assump_82 assump_83 =>
                    cases assump_82
                    case intro assump_84 assump_85 =>
                      apply False.elim assump_84
        case inr assump_63 =>
          cases assump_63
          case intro assump_88 assump_89 =>
            cases assump_3
            case intro assump_96 assump_97 =>
              cases assump_96
              case intro assump_98 assump_99 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  cases assump_100
                  case intro assump_102 assump_103 =>
                    cases assump_99
                    case intro assump_110 assump_111 =>
                      cases assump_110
                      case intro assump_112 assump_113 =>
                        apply False.elim assump_112


variable (p1 p2 p0 p3 p7 p4 p6 : Prop)
theorem file45_35662 : ((((((p7 ∧ True) ∧ (p1 ∨ p1)) ∨ ((p2 ∧ False) ∨ (p0 → False))) ∧ (((p4 ∧ True) → (p6 ∨ p3)) → ((p1 ∧ p6) ∨ (p1 ∧ p0)))) ∧ ((((p7 → False) → False) → ((False ∧ False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case inl assump_16 =>
              have assump_74 : (((p7 → False) → False) → ((False ∧ False) → False)) := by
                intro assump_25
                intro assump_26
                cases assump_26
                case intro assump_27 assump_28 =>
                  apply False.elim assump_27
              let assump_24 := assump_3 assump_74
              apply False.elim assump_24
            case inr assump_17 =>
              have assump_75 : (((p7 → False) → False) → ((False ∧ False) → False)) := by
                intro assump_41
                intro assump_42
                cases assump_42
                case intro assump_43 assump_44 =>
                  apply False.elim assump_43
              let assump_40 := assump_3 assump_75
              apply False.elim assump_40
      case inr assump_7 =>
        cases assump_7
        case inl assump_50 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            apply False.elim assump_53
        case inr assump_51 =>
          have assump_76 : (((p7 → False) → False) → ((False ∧ False) → False)) := by
            intro assump_65
            intro assump_66
            cases assump_66
            case intro assump_67 assump_68 =>
              apply False.elim assump_67
          let assump_64 := assump_3 assump_76
          apply False.elim assump_64


variable (p2 p5 p3 p7 p1 : Prop)
theorem file45_37621 : (((((True → False) → False) → False) → (((p3 → False) ∨ (p3 → False)) → False)) ∨ ((((p7 → p5) ∧ (p2 ∨ p2)) → ((p2 ∧ p1) → (p7 → False))) ∧ (((p3 ∧ False) ∧ (p7 ∨ p3)) → False))) := by
  apply Or.inl
  intro assump_18
  intro assump_19
  cases assump_19
  case inl assump_20 =>
    have assump_52 : ((True → False) → False) := by
      intro assump_27
      have assump_53 : True := by
        apply True.intro
      let assump_30 := assump_27 assump_53
      apply False.elim assump_30
    let assump_26 := assump_18 assump_52
    apply False.elim assump_26
  case inr assump_21 =>
    have assump_54 : ((True → False) → False) := by
      intro assump_42
      have assump_55 : True := by
        apply True.intro
      let assump_45 := assump_42 assump_55
      apply False.elim assump_45
    let assump_41 := assump_18 assump_54
    apply False.elim assump_41


variable (p5 p4 p6 p0 p7 p2 p3 p1 : Prop)
theorem file45_38551 : ((((((True → False) ∧ (p1 → False)) → False) → False) ∧ ((((p2 → p0) ∨ (p6 ∨ p3)) ∨ ((p1 ∨ p4) ∨ (p0 ∧ p3))) ∧ (((p7 ∨ p5) ∧ (False → p6)) → ((True → False) ∧ (p1 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_154 : (((True → False) ∧ (p1 → False)) → False) := by
            intro assump_19
            cases assump_19
            case intro assump_20 assump_21 =>
              have assump_155 : True := by
                apply True.intro
              let assump_27 := assump_20 assump_155
              apply False.elim assump_27
          let assump_18 := assump_2 assump_154
          apply False.elim assump_18
        case inr assump_11 =>
          cases assump_11
          case inl assump_34 =>
            have assump_156 : (((True → False) ∧ (p1 → False)) → False) := by
              intro assump_43
              cases assump_43
              case intro assump_44 assump_45 =>
                have assump_157 : True := by
                  apply True.intro
                let assump_51 := assump_44 assump_157
                apply False.elim assump_51
            let assump_42 := assump_2 assump_156
            apply False.elim assump_42
          case inr assump_35 =>
            have assump_158 : (((True → False) ∧ (p1 → False)) → False) := by
              intro assump_65
              cases assump_65
              case intro assump_66 assump_67 =>
                have assump_159 : True := by
                  apply True.intro
                let assump_73 := assump_66 assump_159
                apply False.elim assump_73
            let assump_64 := assump_2 assump_158
            apply False.elim assump_64
      case inr assump_9 =>
        cases assump_9
        case inl assump_80 =>
          cases assump_80
          case inl assump_82 =>
            have assump_160 : (((True → False) ∧ (p1 → False)) → False) := by
              intro assump_91
              cases assump_91
              case intro assump_92 assump_93 =>
                have assump_161 : p1 := by
                  exact assump_82
                let assump_98 := assump_93 assump_161
                apply False.elim assump_98
            let assump_90 := assump_2 assump_160
            apply False.elim assump_90
          case inr assump_83 =>
            have assump_162 : (((True → False) ∧ (p1 → False)) → False) := by
              intro assump_112
              cases assump_112
              case intro assump_113 assump_114 =>
                have assump_163 : True := by
                  apply True.intro
                let assump_120 := assump_113 assump_163
                apply False.elim assump_120
            let assump_111 := assump_2 assump_162
            apply False.elim assump_111
        case inr assump_81 =>
          cases assump_81
          case intro assump_127 assump_128 =>
            have assump_164 : (((True → False) ∧ (p1 → False)) → False) := by
              intro assump_139
              cases assump_139
              case intro assump_140 assump_141 =>
                have assump_165 : True := by
                  apply True.intro
                let assump_147 := assump_140 assump_165
                apply False.elim assump_147
            let assump_138 := assump_2 assump_164
            apply False.elim assump_138


variable (p0 p6 p7 p5 : Prop)
theorem file45_42113 : ((((((p6 → True) → False) ∧ ((p0 ∧ p0) ∨ (p7 ∨ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_46 : ((((p6 → True) → False) ∧ ((p0 ∧ p0) ∨ (p7 ∨ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_47 : (p6 → True) := by
            intro assump_21
            apply True.intro
          let assump_20 := assump_6 assump_47
          apply False.elim assump_20
      case inr assump_11 =>
        cases assump_11
        case inl assump_25 =>
          have assump_48 : (p6 → True) := by
            intro assump_31
            apply True.intro
          let assump_30 := assump_6 assump_48
          apply False.elim assump_30
        case inr assump_26 =>
          have assump_49 : (p6 → True) := by
            intro assump_39
            apply True.intro
          let assump_38 := assump_6 assump_49
          apply False.elim assump_38
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p2 p7 p1 p3 p0 p6 p4 p5 : Prop)
theorem file45_43288 : ((((((p2 ∧ p0) ∨ (p5 ∧ False)) ∧ ((p7 → False) ∧ (p0 ∨ p4))) ∨ (((p6 ∧ True) → (p1 ∨ p5)) → False)) ∧ ((((False ∧ True) ∨ (p3 → p3)) → ((p7 → p7) ∨ (p1 ∧ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_17
              case inl assump_20 =>
                have assump_88 : (((False ∧ True) ∨ (p3 → p3)) → ((p7 → p7) ∨ (p1 ∧ p4))) := by
                  intro assump_27
                  cases assump_27
                  case inl assump_28 =>
                    cases assump_28
                    case intro assump_30 assump_31 =>
                      apply False.elim assump_30
                  case inr assump_29 =>
                    apply Or.inl
                    intro assump_36
                    exact assump_36
                let assump_26 := assump_3 assump_88
                apply False.elim assump_26
              case inr assump_21 =>
                have assump_89 : (((False ∧ True) ∨ (p3 → p3)) → ((p7 → p7) ∨ (p1 ∧ p4))) := by
                  intro assump_47
                  cases assump_47
                  case inl assump_48 =>
                    cases assump_48
                    case intro assump_50 assump_51 =>
                      apply False.elim assump_50
                  case inr assump_49 =>
                    apply Or.inl
                    intro assump_56
                    exact assump_56
                let assump_46 := assump_3 assump_89
                apply False.elim assump_46
        case inr assump_9 =>
          cases assump_9
          case intro assump_62 assump_63 =>
            apply False.elim assump_63
    case inr assump_5 =>
      have assump_90 : (((False ∧ True) ∨ (p3 → p3)) → ((p7 → p7) ∨ (p1 ∧ p4))) := by
        intro assump_73
        cases assump_73
        case inl assump_74 =>
          cases assump_74
          case intro assump_76 assump_77 =>
            apply False.elim assump_76
        case inr assump_75 =>
          apply Or.inl
          intro assump_82
          exact assump_82
      let assump_72 := assump_3 assump_90
      apply False.elim assump_72


variable (p2 p5 p0 p1 p4 p6 : Prop)
theorem file45_45781 : ((((((True ∧ True) ∧ (p1 → False)) ∨ ((True → False) → False)) → False) ∧ ((((p6 → False) → False) → False) ∧ (((True → False) ∧ (p4 → p2)) ∧ ((p2 ∨ p0) ∧ (False ∧ p5))))) → False) := by
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
            case inl assump_20 =>
              cases assump_19
              case intro assump_24 assump_25 =>
                apply False.elim assump_24
            case inr assump_21 =>
              cases assump_19
              case intro assump_30 assump_31 =>
                apply False.elim assump_30


variable (p4 p5 p1 p2 p6 p3 : Prop)
theorem file45_46686 : ((((((p3 ∨ p2) ∧ (p6 ∧ False)) → False) ∧ (((False → p1) ∨ (p1 → True)) ∨ ((True ∧ p5) → (p3 ∨ p4)))) → False) → False) := by
  intro assump_15
  have assump_46 : ((((p3 ∨ p2) ∧ (p6 ∧ False)) → False) ∧ (((False → p1) ∨ (p1 → True)) ∨ ((True ∧ p5) → (p3 ∨ p4)))) := by
    apply And.intro
    intro assump_19
    cases assump_19
    case intro assump_20 assump_21 =>
      cases assump_20
      case inl assump_22 =>
        cases assump_21
        case intro assump_26 assump_27 =>
          apply False.elim assump_27
      case inr assump_23 =>
        cases assump_21
        case intro assump_34 assump_35 =>
          apply False.elim assump_35
    apply Or.inl
    apply Or.inl
    intro assump_40
    apply False.elim assump_40
  let assump_18 := assump_15 assump_46
  apply False.elim assump_18


variable (p7 p3 p5 p0 p4 p2 p6 : Prop)
theorem file45_47553 : (((((p4 → False) → (p7 ∨ True)) ∨ ((p4 → p0) ∧ (p6 ∨ p5))) ∨ (((p2 → False) ∧ (p6 → p6)) → False)) ∨ ((((p0 → False) → False) → ((p3 → p2) ∧ (p6 ∧ p6))) ∧ (((p4 ∧ p7) ∨ (p7 ∨ p0)) ∨ ((False → False) ∧ (p4 ∨ False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p4 p2 p3 p5 p7 p1 : Prop)
theorem file45_47933 : (((((p7 ∧ p5) → (True → False)) ∧ ((p1 → False) → False)) → False) → ((((p1 ∧ p7) ∨ (p5 ∧ p5)) → ((p4 ∨ p3) → (p3 ∨ p4))) ∨ (((p5 ∨ False) → False) ∨ ((p2 ∨ p2) ∧ (p5 ∧ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    cases assump_4
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply Or.inr
        exact assump_6
    case inr assump_11 =>
      cases assump_11
      case intro assump_18 assump_19 =>
        apply Or.inr
        exact assump_6
  case inr assump_7 =>
    cases assump_4
    case inl assump_26 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        apply Or.inl
        exact assump_7
    case inr assump_27 =>
      cases assump_27
      case intro assump_34 assump_35 =>
        apply Or.inl
        exact assump_7


variable (p6 p1 p5 p0 p3 p2 : Prop)
theorem file45_48874 : (((((p5 ∧ True) ∨ (p0 → False)) → False) → False) → ((((p2 ∧ p5) → (p3 ∧ p1)) → ((p6 → False) → False)) → (((p3 ∧ False) ∧ (True → p0)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p2 p4 : Prop)
theorem file45_49264 : ((((((p4 → True) ∨ (p2 → True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : ((((p4 → True) ∨ (p2 → True)) → False) → False) := by
    intro assump_5
    have assump_17 : ((p4 → True) ∨ (p2 → True)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p1 p5 p6 p3 p4 p7 p2 : Prop)
theorem file45_49765 : (((((p3 ∧ False) ∧ (p4 ∨ False)) ∧ ((p0 → p4) → False)) → (((p2 → p0) → False) ∨ ((True → p6) ∨ (True → p1)))) ∨ ((((True ∧ True) → (p6 ∧ False)) ∨ ((p7 ∨ p1) → (p4 ∧ p5))) ∧ (((True ∧ p7) → (True ∧ p2)) ∨ ((p7 → p4) ∨ (p3 ∧ p3))))) := by
  apply Or.inl
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        apply False.elim assump_15


variable (p5 p6 p0 p7 p1 p2 : Prop)
theorem file45_50304 : ((((((p2 ∨ p6) ∧ (True ∧ False)) ∧ ((p7 ∨ True) → (p2 ∧ p5))) → (((p7 ∧ p1) → False) ∧ ((p0 ∨ False) ∨ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p2 ∨ p6) ∧ (True ∧ False)) ∧ ((p7 ∨ True) → (p2 ∧ p5))) → (((p7 ∧ p1) → False) ∧ ((p0 ∨ False) ∨ (p6 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_15
          case inl assump_17 =>
            cases assump_16
            case intro assump_21 assump_22 =>
              apply False.elim assump_22
          case inr assump_18 =>
            cases assump_16
            case intro assump_29 assump_30 =>
              apply False.elim assump_30
    cases assump_5
    case intro assump_35 assump_36 =>
      cases assump_35
      case intro assump_37 assump_38 =>
        cases assump_37
        case inl assump_39 =>
          cases assump_38
          case intro assump_43 assump_44 =>
            apply False.elim assump_44
        case inr assump_40 =>
          cases assump_38
          case intro assump_51 assump_52 =>
            apply False.elim assump_52
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p2 p3 p4 p6 : Prop)
theorem file45_51706 : (((((True ∧ p2) → (p4 ∧ p3)) → ((p2 ∨ p6) → (p6 ∨ True))) → False) → False) := by
  intro assump_10
  have assump_29 : (((True ∧ p2) → (p4 ∧ p3)) → ((p2 ∨ p6) → (p6 ∨ True))) := by
    intro assump_14
    intro assump_15
    cases assump_15
    case inl assump_16 =>
      apply Or.inr
      apply True.intro
    case inr assump_17 =>
      apply Or.inl
      exact assump_17
  let assump_13 := assump_10 assump_29
  apply False.elim assump_13


variable (p1 p7 p3 p0 : Prop)
theorem file45_52204 : ((((((True ∧ p3) ∨ (p3 → p3)) ∨ ((p7 ∨ True) → False)) ∨ (((p0 ∧ p1) → (True → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((True ∧ p3) ∨ (p3 → p3)) ∨ ((p7 ∨ True) → False)) ∨ (((p0 ∧ p1) → (True → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p6 p1 p4 : Prop)
theorem file45_52670 : ((((((p1 ∧ p7) → (p7 → p6)) → ((False → p4) ∨ (p1 → False))) ∨ (((p7 → False) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 ∧ p7) → (p7 → p6)) → ((False → p4) ∨ (p1 → False))) ∨ (((p7 → False) → False) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p7 p2 p5 p3 p0 p1 : Prop)
theorem file45_53158 : ((((((p1 → True) → False) ∨ ((p1 → p2) ∨ (p0 ∨ p2))) ∨ (((p5 ∧ p2) ∧ (p5 → False)) → False)) ∧ ((((p0 → False) → (p0 ∧ p2)) ∨ ((p6 → False) ∨ (p1 ∧ p5))) ∧ (((False → p5) → False) ∧ ((p2 ∧ p7) → (p3 ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_11
            case intro assump_16 assump_17 =>
              have assump_312 : (False → p5) := by
                intro assump_24
                apply False.elim assump_24
              let assump_23 := assump_16 assump_312
              apply False.elim assump_23
          case inr assump_13 =>
            cases assump_13
            case inl assump_30 =>
              cases assump_11
              case intro assump_34 assump_35 =>
                have assump_313 : (False → p5) := by
                  intro assump_42
                  apply False.elim assump_42
                let assump_41 := assump_34 assump_313
                apply False.elim assump_41
            case inr assump_31 =>
              cases assump_31
              case intro assump_48 assump_49 =>
                cases assump_11
                case intro assump_54 assump_55 =>
                  have assump_314 : (False → p5) := by
                    intro assump_62
                    apply False.elim assump_62
                  let assump_61 := assump_54 assump_314
                  apply False.elim assump_61
      case inr assump_7 =>
        cases assump_7
        case inl assump_68 =>
          cases assump_3
          case intro assump_72 assump_73 =>
            cases assump_72
            case inl assump_74 =>
              cases assump_73
              case intro assump_78 assump_79 =>
                have assump_315 : (False → p5) := by
                  intro assump_86
                  apply False.elim assump_86
                let assump_85 := assump_78 assump_315
                apply False.elim assump_85
            case inr assump_75 =>
              cases assump_75
              case inl assump_92 =>
                cases assump_73
                case intro assump_96 assump_97 =>
                  have assump_316 : (False → p5) := by
                    intro assump_104
                    apply False.elim assump_104
                  let assump_103 := assump_96 assump_316
                  apply False.elim assump_103
              case inr assump_93 =>
                cases assump_93
                case intro assump_110 assump_111 =>
                  cases assump_73
                  case intro assump_116 assump_117 =>
                    have assump_317 : (False → p5) := by
                      intro assump_124
                      apply False.elim assump_124
                    let assump_123 := assump_116 assump_317
                    apply False.elim assump_123
        case inr assump_69 =>
          cases assump_69
          case inl assump_130 =>
            cases assump_3
            case intro assump_134 assump_135 =>
              cases assump_134
              case inl assump_136 =>
                cases assump_135
                case intro assump_140 assump_141 =>
                  have assump_318 : (False → p5) := by
                    intro assump_148
                    apply False.elim assump_148
                  let assump_147 := assump_140 assump_318
                  apply False.elim assump_147
              case inr assump_137 =>
                cases assump_137
                case inl assump_154 =>
                  cases assump_135
                  case intro assump_158 assump_159 =>
                    have assump_319 : (False → p5) := by
                      intro assump_166
                      apply False.elim assump_166
                    let assump_165 := assump_158 assump_319
                    apply False.elim assump_165
                case inr assump_155 =>
                  cases assump_155
                  case intro assump_172 assump_173 =>
                    cases assump_135
                    case intro assump_178 assump_179 =>
                      have assump_320 : (False → p5) := by
                        intro assump_186
                        apply False.elim assump_186
                      let assump_185 := assump_178 assump_320
                      apply False.elim assump_185
          case inr assump_131 =>
            cases assump_3
            case intro assump_194 assump_195 =>
              cases assump_194
              case inl assump_196 =>
                cases assump_195
                case intro assump_200 assump_201 =>
                  have assump_321 : (False → p5) := by
                    intro assump_208
                    apply False.elim assump_208
                  let assump_207 := assump_200 assump_321
                  apply False.elim assump_207
              case inr assump_197 =>
                cases assump_197
                case inl assump_214 =>
                  cases assump_195
                  case intro assump_218 assump_219 =>
                    have assump_322 : (False → p5) := by
                      intro assump_226
                      apply False.elim assump_226
                    let assump_225 := assump_218 assump_322
                    apply False.elim assump_225
                case inr assump_215 =>
                  cases assump_215
                  case intro assump_232 assump_233 =>
                    cases assump_195
                    case intro assump_238 assump_239 =>
                      have assump_323 : (False → p5) := by
                        intro assump_246
                        apply False.elim assump_246
                      let assump_245 := assump_238 assump_323
                      apply False.elim assump_245
    case inr assump_5 =>
      cases assump_3
      case intro assump_254 assump_255 =>
        cases assump_254
        case inl assump_256 =>
          cases assump_255
          case intro assump_260 assump_261 =>
            have assump_324 : (False → p5) := by
              intro assump_268
              apply False.elim assump_268
            let assump_267 := assump_260 assump_324
            apply False.elim assump_267
        case inr assump_257 =>
          cases assump_257
          case inl assump_274 =>
            cases assump_255
            case intro assump_278 assump_279 =>
              have assump_325 : (False → p5) := by
                intro assump_286
                apply False.elim assump_286
              let assump_285 := assump_278 assump_325
              apply False.elim assump_285
          case inr assump_275 =>
            cases assump_275
            case intro assump_292 assump_293 =>
              cases assump_255
              case intro assump_298 assump_299 =>
                have assump_326 : (False → p5) := by
                  intro assump_306
                  apply False.elim assump_306
                let assump_305 := assump_298 assump_326
                apply False.elim assump_305


variable (p7 p1 p4 p2 p3 p6 p0 : Prop)
theorem file45_60448 : (((((False ∧ p7) ∧ (p2 ∧ p6)) → False) ∨ (((p6 ∧ p4) → False) → False)) ∨ ((((p0 → p3) → False) → False) ∨ (((p1 ∨ p0) ∨ (p2 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p6 p7 p5 p3 : Prop)
theorem file45_60839 : (((((p5 → False) ∧ (p3 → p3)) → False) ∧ (((True → False) ∧ (False ∨ p5)) ∧ ((p7 ∧ p6) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          have assump_26 : True := by
            apply True.intro
          let assump_22 := assump_8 assump_26
          apply False.elim assump_22


variable (p1 p5 p6 p4 p0 p3 p2 : Prop)
theorem file45_61467 : (((((True ∨ False) → False) ∧ ((True → False) ∨ (p4 ∨ p6))) → (((p2 → False) → False) ∨ ((p3 → p3) → (p3 ∨ p5)))) ∨ ((((p1 ∧ p6) → (p2 → False)) ∧ ((p0 → False) ∨ (True ∨ True))) → (((p4 → False) ∧ (p1 → False)) ∧ ((False → p6) ∧ (p5 ∨ p4))))) := by
  apply Or.inl
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_28
    case inl assump_31 =>
      apply Or.inl
      intro assump_35
      have assump_67 : True := by
        apply True.intro
      let assump_39 := assump_31 assump_67
      apply False.elim assump_39
    case inr assump_32 =>
      cases assump_32
      case inl assump_43 =>
        apply Or.inl
        intro assump_47
        have assump_68 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_52 := assump_27 assump_68
        apply False.elim assump_52
      case inr assump_44 =>
        apply Or.inl
        intro assump_58
        have assump_69 : (True ∨ False) := by
          apply Or.inl
          apply True.intro
        let assump_63 := assump_27 assump_69
        apply False.elim assump_63


variable (p7 p6 p3 p2 p1 p0 : Prop)
theorem file45_62632 : ((((((p0 → p0) ∧ (p3 ∨ p1)) → False) → False) ∧ ((((p2 → False) → (p6 → p1)) → ((p2 → p2) ∨ (p7 ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_18 : (((p2 → False) → (p6 → p1)) → ((p2 → p2) ∨ (p7 ∨ False))) := by
      intro assump_9
      apply Or.inl
      intro assump_12
      exact assump_12
    let assump_8 := assump_3 assump_18
    apply False.elim assump_8


variable (p1 p0 p2 p5 p7 p4 p6 p3 : Prop)
theorem file45_63136 : (((((False ∨ p5) ∧ (p6 ∨ p0)) ∨ ((p7 ∨ True) → (p2 ∨ p4))) ∨ (((True ∧ True) ∧ (True ∨ p7)) → ((p3 → p4) → False))) → ((((True ∨ p2) ∨ (False ∧ p5)) ∨ ((p6 → p4) ∧ (p4 → False))) ∨ (((p6 ∧ p0) ∧ (p7 ∨ True)) ∧ ((p0 → p1) ∨ (p0 → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          apply False.elim assump_8
        case inr assump_9 =>
          cases assump_7
          case inl assump_14 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
          case inr assump_15 =>
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply Or.inl
            apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
  case inr assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro


variable (p0 p3 p5 p1 p4 p2 p6 : Prop)
theorem file45_64305 : (((((p0 → False) → False) ∨ ((p3 ∧ p1) → False)) → (((True → p5) → (p0 → p4)) → ((p6 → False) ∧ (p5 → False)))) → ((((False → p3) → False) → False) ∨ (((True → False) ∨ (p2 ∨ p1)) → ((True ∧ p4) ∨ (True ∧ p4))))) := by
  intro assump_35
  apply Or.inl
  intro assump_38
  have assump_48 : (False → p3) := by
    intro assump_42
    apply False.elim assump_42
  let assump_41 := assump_38 assump_48
  apply False.elim assump_41


variable (p7 p0 p4 p1 p5 : Prop)
theorem file45_64789 : ((((((p4 ∨ p7) ∨ (p7 ∧ p4)) ∧ ((p0 ∧ p1) ∧ (p4 ∧ p4))) → (((p1 ∨ p5) → False) → ((False ∧ p0) ∧ (p7 → p0)))) → False) → False) := by
  intro assump_21
  have assump_241 : ((((p4 ∨ p7) ∨ (p7 ∧ p4)) ∧ ((p0 ∧ p1) ∧ (p4 ∧ p4))) → (((p1 ∨ p5) → False) → ((False ∧ p0) ∧ (p7 → p0)))) := by
    intro assump_25
    intro assump_26
    apply And.intro
    apply And.intro
    cases assump_25
    case intro assump_29 assump_30 =>
      cases assump_29
      case inl assump_31 =>
        cases assump_31
        case inl assump_33 =>
          cases assump_30
          case intro assump_37 assump_38 =>
            cases assump_37
            case intro assump_39 assump_40 =>
              cases assump_38
              case intro assump_45 assump_46 =>
                have assump_242 : (p1 ∨ p5) := by
                  apply Or.inl
                  exact assump_40
                let assump_56 := assump_26 assump_242
                apply False.elim assump_56
        case inr assump_34 =>
          cases assump_30
          case intro assump_62 assump_63 =>
            cases assump_62
            case intro assump_64 assump_65 =>
              cases assump_63
              case intro assump_70 assump_71 =>
                have assump_243 : (p1 ∨ p5) := by
                  apply Or.inl
                  exact assump_65
                let assump_81 := assump_26 assump_243
                apply False.elim assump_81
      case inr assump_32 =>
        cases assump_32
        case intro assump_85 assump_86 =>
          cases assump_30
          case intro assump_91 assump_92 =>
            cases assump_91
            case intro assump_93 assump_94 =>
              cases assump_92
              case intro assump_99 assump_100 =>
                have assump_244 : (p1 ∨ p5) := by
                  apply Or.inl
                  exact assump_94
                let assump_111 := assump_26 assump_244
                apply False.elim assump_111
    cases assump_25
    case intro assump_117 assump_118 =>
      cases assump_117
      case inl assump_119 =>
        cases assump_119
        case inl assump_121 =>
          cases assump_118
          case intro assump_125 assump_126 =>
            cases assump_125
            case intro assump_127 assump_128 =>
              cases assump_126
              case intro assump_133 assump_134 =>
                exact assump_127
        case inr assump_122 =>
          cases assump_118
          case intro assump_141 assump_142 =>
            cases assump_141
            case intro assump_143 assump_144 =>
              cases assump_142
              case intro assump_149 assump_150 =>
                exact assump_143
      case inr assump_120 =>
        cases assump_120
        case intro assump_155 assump_156 =>
          cases assump_118
          case intro assump_161 assump_162 =>
            cases assump_161
            case intro assump_163 assump_164 =>
              cases assump_162
              case intro assump_169 assump_170 =>
                exact assump_163
    intro assump_175
    cases assump_25
    case intro assump_180 assump_181 =>
      cases assump_180
      case inl assump_182 =>
        cases assump_182
        case inl assump_184 =>
          cases assump_181
          case intro assump_188 assump_189 =>
            cases assump_188
            case intro assump_190 assump_191 =>
              cases assump_189
              case intro assump_196 assump_197 =>
                exact assump_190
        case inr assump_185 =>
          cases assump_181
          case intro assump_204 assump_205 =>
            cases assump_204
            case intro assump_206 assump_207 =>
              cases assump_205
              case intro assump_212 assump_213 =>
                exact assump_206
      case inr assump_183 =>
        cases assump_183
        case intro assump_218 assump_219 =>
          cases assump_181
          case intro assump_224 assump_225 =>
            cases assump_224
            case intro assump_226 assump_227 =>
              cases assump_225
              case intro assump_232 assump_233 =>
                exact assump_226
  let assump_24 := assump_21 assump_241
  apply False.elim assump_24


variable (p0 p5 p2 p3 p7 p4 p6 : Prop)
theorem file45_69075 : (((((p6 ∨ p2) ∧ (True ∨ p6)) → ((p5 ∧ False) → (p0 → p6))) ∨ (((p4 ∨ p3) → False) → ((p0 ∨ p5) ∧ (p7 → False)))) ∨ ((((p6 ∨ p2) ∨ (True → p2)) ∨ ((False → False) ∨ (p3 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p5 p3 p4 p1 p7 p2 p0 p6 : Prop)
theorem file45_69498 : ((((((p3 ∧ p0) ∧ (p2 → p7)) ∨ ((p6 ∨ False) → (p4 ∨ True))) → False) ∧ ((((p1 ∨ p2) ∧ (p5 ∨ p5)) ∧ ((p5 ∨ p4) ∧ (p0 → p3))) → (((p1 ∧ p0) → (False ∧ False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((p3 ∧ p0) ∧ (p2 → p7)) ∨ ((p6 ∨ False) → (p4 ∨ True))) := by
      apply Or.inr
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        apply Or.inr
        apply True.intro
      case inr assump_12 =>
        apply False.elim assump_12
    let assump_9 := assump_2 assump_20
    apply False.elim assump_9


variable (p7 p2 : Prop)
theorem file45_70150 : ((((((True ∨ p7) → False) → False) ∨ (((p2 → p7) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p7) → False) → False) ∨ (((p2 → p7) → False) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p7) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p2 p1 p3 p6 : Prop)
theorem file45_70658 : (((((p2 ∧ False) → (p4 ∨ p1)) ∨ ((p3 → False) ∧ (False ∨ True))) ∨ (((p3 ∧ p6) → False) ∧ ((p4 → p2) ∨ (False → p3)))) ∨ ((((p4 ∧ p6) → False) ∧ ((p6 → True) → False)) → (((p6 ∨ p1) ∨ (p4 ∧ p2)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_3


variable (p7 p1 p3 p4 : Prop)
theorem file45_71067 : ((((((True ∨ p4) → False) → False) ∨ (((p1 → False) → (p3 ∨ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p4) → False) → False) ∨ (((p1 → False) → (p3 ∨ p7)) → False)) := by
    apply Or.inl
    intro assump_5
    have assump_16 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p1 p0 p6 p4 p2 : Prop)
theorem file45_71592 : (((((p4 ∨ p1) → False) → ((True → True) ∨ (p1 → False))) ∨ (((p0 ∧ p4) ∧ (p6 ∨ p0)) → False)) ∨ ((((p7 → False) ∨ (p7 → True)) → ((p6 → False) → (p4 → False))) ∧ (((p2 → p4) ∧ (p0 ∧ p0)) ∨ ((True ∧ False) ∧ (p7 ∧ p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_21
  apply Or.inl
  intro assump_24
  apply True.intro


variable (p6 p0 p3 p2 p4 p7 p5 : Prop)
theorem file45_71982 : (((((p5 → p7) → (p6 ∨ False)) → False) → (((p2 → p2) ∨ (p4 → False)) ∨ ((p6 ∧ p4) → (p0 → False)))) ∨ ((((p3 ∧ p3) → (p4 → p2)) → False) → False)) := by
  apply Or.inl
  intro assump_35
  apply Or.inl
  apply Or.inl
  intro assump_38
  exact assump_38


variable (p2 p5 p3 p6 p0 p7 p4 : Prop)
theorem file45_72297 : (((((p2 → False) ∨ (True ∨ True)) → False) ∧ (((p7 → False) → (p4 → False)) → False)) → ((((p5 ∧ p3) → (p7 → p5)) → ((False → False) ∨ (True ∨ p3))) ∨ (((p0 → p2) → (p4 ∧ p7)) → ((p6 → p4) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    apply Or.inl
    intro assump_11
    apply False.elim assump_11


variable (p3 : Prop)
theorem file45_72721 : ((((((True ∨ p3) → (True ∨ False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True ∨ p3) → (True ∨ False)) → False) → False) := by
    intro assump_5
    have assump_23 : ((True ∨ p3) → (True ∨ False)) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        apply True.intro
      case inr assump_11 =>
        apply Or.inl
        apply True.intro
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p3 p1 p6 p5 p2 p7 p0 : Prop)
theorem file45_73355 : (((((p7 ∨ p5) → (False ∨ p7)) ∧ ((p6 → False) ∧ (p1 ∧ False))) ∧ (((p3 → False) → False) → ((p2 → p0) → False))) → ((((p0 → p7) → (False ∨ p3)) → False) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_12
      case intro assump_15 assump_16 =>
        cases assump_16
        case intro assump_19 assump_20 =>
          apply False.elim assump_20


variable (p3 p0 p7 p6 p5 p1 : Prop)
theorem file45_73892 : (((((p0 → False) → (False → p5)) → ((p3 → p6) → (p7 → True))) ∨ (((p3 → False) → (p1 → False)) ∧ ((p1 ∧ p3) ∨ (p7 ∧ p7)))) ∨ ((((p3 → p6) → (p0 → False)) → False) ∨ (((p1 → p5) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro


variable (p5 p3 p1 p7 p4 p6 p0 : Prop)
theorem file45_74258 : ((((((p5 ∨ False) ∧ (p1 → False)) → ((p0 → False) → (True ∨ p0))) ∨ (((p7 → p0) ∨ (False → p4)) ∨ ((p3 ∨ False) ∨ (p6 ∨ p1)))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p5 ∨ False) ∧ (p1 → False)) → ((p0 → False) → (True ∨ p0))) ∨ (((p7 → p0) ∨ (False → p4)) ∨ ((p3 ∨ False) ∨ (p6 ∨ p1)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        apply Or.inl
        apply True.intro
      case inr assump_12 =>
        apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p0 p3 p2 p5 : Prop)
theorem file45_74964 : (((((False ∧ p2) ∧ (p0 ∧ p5)) ∧ ((p3 → False) ∨ (p2 → False))) ∧ (((p5 ∧ False) ∨ (p0 → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          apply False.elim assump_8


variable (p4 p2 p7 p0 p6 p1 p3 : Prop)
theorem file45_75429 : (((((p1 → p7) → (False ∧ p6)) ∧ ((False → p3) ∧ (False → p6))) ∨ (((p7 → False) → (p7 → p4)) → ((p3 ∨ p6) ∨ (True ∨ p6)))) → ((((p4 → False) ∨ (p3 → False)) ∨ ((p1 ∧ p0) ∨ (p4 → False))) → (((True ∨ p1) ∨ (p2 ∨ p3)) ∧ ((p2 → p2) ∨ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_12
          case intro assump_15 assump_16 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_10 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
    case inr assump_6 =>
      cases assump_1
      case inl assump_25 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_28
          case intro assump_31 assump_32 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_26 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  case inr assump_4 =>
    cases assump_4
    case inl assump_39 =>
      cases assump_39
      case intro assump_41 assump_42 =>
        cases assump_1
        case inl assump_47 =>
          cases assump_47
          case intro assump_49 assump_50 =>
            cases assump_50
            case intro assump_53 assump_54 =>
              apply Or.inl
              apply Or.inl
              apply True.intro
        case inr assump_48 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
    case inr assump_40 =>
      cases assump_1
      case inl assump_63 =>
        cases assump_63
        case intro assump_65 assump_66 =>
          cases assump_66
          case intro assump_69 assump_70 =>
            apply Or.inl
            apply Or.inl
            apply True.intro
      case inr assump_64 =>
        apply Or.inl
        apply Or.inl
        apply True.intro
  cases assump_2
  case inl assump_77 =>
    cases assump_77
    case inl assump_79 =>
      cases assump_1
      case inl assump_83 =>
        cases assump_83
        case intro assump_85 assump_86 =>
          cases assump_86
          case intro assump_89 assump_90 =>
            apply Or.inl
            intro assump_95
            exact assump_95
      case inr assump_84 =>
        apply Or.inl
        intro assump_100
        exact assump_100
    case inr assump_80 =>
      cases assump_1
      case inl assump_105 =>
        cases assump_105
        case intro assump_107 assump_108 =>
          cases assump_108
          case intro assump_111 assump_112 =>
            apply Or.inl
            intro assump_117
            exact assump_117
      case inr assump_106 =>
        apply Or.inl
        intro assump_122
        exact assump_122
  case inr assump_78 =>
    cases assump_78
    case inl assump_125 =>
      cases assump_125
      case intro assump_127 assump_128 =>
        cases assump_1
        case inl assump_133 =>
          cases assump_133
          case intro assump_135 assump_136 =>
            cases assump_136
            case intro assump_139 assump_140 =>
              apply Or.inl
              intro assump_145
              exact assump_145
        case inr assump_134 =>
          apply Or.inl
          intro assump_150
          exact assump_150
    case inr assump_126 =>
      cases assump_1
      case inl assump_155 =>
        cases assump_155
        case intro assump_157 assump_158 =>
          cases assump_158
          case intro assump_161 assump_162 =>
            apply Or.inl
            intro assump_167
            exact assump_167
      case inr assump_156 =>
        apply Or.inl
        intro assump_172
        exact assump_172


variable (p0 p4 p3 p2 p5 p7 p6 : Prop)
theorem file45_79315 : (((((p3 ∨ p6) ∨ (p5 ∨ p6)) → False) ∨ (((p4 ∨ p4) ∧ (False ∨ p7)) → ((p3 → p2) → (p5 ∧ p0)))) → ((((False ∧ p7) → (p0 → False)) → False) → False)) := by
  intro assump_11
  intro assump_12
  cases assump_11
  case inl assump_15 =>
    have assump_47 : ((False ∧ p7) → (p0 → False)) := by
      intro assump_21
      intro assump_22
      cases assump_21
      case intro assump_25 assump_26 =>
        apply False.elim assump_25
    let assump_20 := assump_12 assump_47
    apply False.elim assump_20
  case inr assump_16 =>
    have assump_48 : ((False ∧ p7) → (p0 → False)) := by
      intro assump_36
      intro assump_37
      cases assump_36
      case intro assump_40 assump_41 =>
        apply False.elim assump_40
    let assump_35 := assump_12 assump_48
    apply False.elim assump_35


variable (p2 p0 p4 p7 p6 p5 p1 p3 : Prop)
theorem file45_80176 : (((((p2 ∧ p0) ∨ (p1 ∨ p5)) ∧ ((False ∧ p3) ∨ (p4 ∨ True))) ∧ (((p7 → p2) ∧ (p5 → p3)) → ((p1 → p2) → (p2 → p0)))) → ((((p7 ∧ False) ∧ (p5 → False)) ∧ ((True ∧ p5) → (p6 ∧ p0))) → (((p7 → True) ∨ (p6 → False)) ∨ ((p2 ∨ p3) ∨ (True → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_8


variable (p5 p2 p3 p6 p0 p1 p4 p7 : Prop)
theorem file45_80724 : ((((((p4 ∧ p6) → (p5 → p1)) → ((p5 → False) → (p3 → False))) ∨ (((p4 ∧ True) → False) ∨ ((p1 ∨ p0) ∨ (False ∨ p4)))) ∧ ((((p2 ∨ p6) ∨ (p0 ∨ p3)) → ((p4 → p2) → (True ∧ p6))) ∧ (((False → False) → False) ∧ ((p7 ∧ p4) → (p4 → p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_116 : (False → False) := by
            intro assump_20
            apply False.elim assump_20
          let assump_19 := assump_12 assump_116
          apply False.elim assump_19
    case inr assump_5 =>
      cases assump_5
      case inl assump_26 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            have assump_117 : (False → False) := by
              intro assump_42
              apply False.elim assump_42
            let assump_41 := assump_34 assump_117
            apply False.elim assump_41
      case inr assump_27 =>
        cases assump_27
        case inl assump_48 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_3
            case intro assump_54 assump_55 =>
              cases assump_55
              case intro assump_58 assump_59 =>
                have assump_118 : (False → False) := by
                  intro assump_66
                  apply False.elim assump_66
                let assump_65 := assump_58 assump_118
                apply False.elim assump_65
          case inr assump_51 =>
            cases assump_3
            case intro assump_74 assump_75 =>
              cases assump_75
              case intro assump_78 assump_79 =>
                have assump_119 : (False → False) := by
                  intro assump_86
                  apply False.elim assump_86
                let assump_85 := assump_78 assump_119
                apply False.elim assump_85
        case inr assump_49 =>
          cases assump_49
          case inl assump_92 =>
            apply False.elim assump_92
          case inr assump_93 =>
            cases assump_3
            case intro assump_98 assump_99 =>
              cases assump_99
              case intro assump_102 assump_103 =>
                have assump_120 : (False → False) := by
                  intro assump_110
                  apply False.elim assump_110
                let assump_109 := assump_102 assump_120
                apply False.elim assump_109


variable (p4 p0 p6 p1 p7 p2 p5 : Prop)
theorem file45_83380 : (((((p2 ∨ p5) ∨ (p0 → p7)) → ((p2 → True) ∧ (True ∨ p7))) → False) → ((((p2 ∨ True) → False) → False) → (((p0 → False) ∧ (p5 ∧ p4)) → ((p5 → p4) ∧ (p6 → p1))))) := by
  intro assump_9
  intro assump_10
  intro assump_11
  apply And.intro
  intro assump_12
  cases assump_11
  case intro assump_15 assump_16 =>
    cases assump_16
    case intro assump_19 assump_20 =>
      exact assump_20
  intro assump_29
  cases assump_11
  case intro assump_32 assump_33 =>
    cases assump_33
    case intro assump_36 assump_37 =>
      have assump_62 : (((p2 ∨ p5) ∨ (p0 → p7)) → ((p2 → True) ∧ (True ∨ p7))) := by
        intro assump_47
        apply And.intro
        intro assump_48
        apply True.intro
        cases assump_47
        case inl assump_49 =>
          cases assump_49
          case inl assump_51 =>
            apply Or.inl
            apply True.intro
          case inr assump_52 =>
            apply Or.inl
            apply True.intro
        case inr assump_50 =>
          apply Or.inl
          apply True.intro
      let assump_46 := assump_9 assump_62
      apply False.elim assump_46


variable (p5 p7 p4 p0 p3 p6 p2 p1 : Prop)
theorem file45_84555 : (((((p3 ∧ p7) → (True ∧ p2)) → ((p6 → p2) → (True ∧ p0))) → (((p7 → False) → False) → ((p7 → True) ∨ (True ∧ False)))) ∧ ((((True ∨ p4) → False) ∨ ((p7 → p7) ∨ (False ∨ p5))) → (((True ∨ p1) ∨ (p3 → p6)) ∨ ((p4 ∧ p0) ∧ (p5 → p0))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply True.intro
  intro assump_8
  cases assump_8
  case inl assump_9 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_10 =>
    cases assump_10
    case inl assump_13 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_14 =>
      cases assump_14
      case inl assump_17 =>
        apply False.elim assump_17
      case inr assump_18 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p6 p2 p5 p3 p4 p7 p0 : Prop)
theorem file45_85466 : ((((((p6 ∧ p7) → (False → False)) ∨ ((p6 → False) → (p0 → False))) ∨ (((p4 ∧ p0) ∨ (p5 ∨ p6)) ∨ ((False → p2) ∧ (p0 → p3)))) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p6 ∧ p7) → (False → False)) ∨ ((p6 → False) → (p0 → False))) ∨ (((p4 ∧ p0) ∨ (p5 ∨ p6)) ∨ ((False → p2) ∧ (p0 → p3)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p7 p1 p0 p2 p6 p3 p5 : Prop)
theorem file45_86010 : (((((p6 → p2) ∨ (p7 → p1)) → ((True ∨ p7) → False)) ∧ (((p7 ∨ p1) → (True → p0)) → ((p1 → p3) ∧ (p5 → False)))) → ((((p7 ∧ p6) ∧ (p5 ∧ False)) → False) ∨ (((True → False) ∨ (False → False)) → ((p1 ∨ p5) ∨ (p5 ∨ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply False.elim assump_18


variable (p0 p6 p3 p1 p5 : Prop)
theorem file45_86616 : (((((p3 → p0) → (True ∧ p5)) → ((p5 → p1) → (True ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p3 → p0) → (True ∧ p5)) → ((p5 → p1) → (True ∨ p6))) := by
    intro assump_5
    intro assump_6
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p3 p2 p0 p6 p1 p7 p4 : Prop)
theorem file45_87003 : (((((p3 → False) → (p3 ∨ p7)) → ((p4 → False) → False)) ∧ (((p2 ∨ p6) → False) ∧ ((False → p5) → False))) → ((((p1 ∧ p0) ∧ (p0 ∧ True)) → False) → (((p7 ∨ True) ∧ (p2 ∧ True)) → ((p1 ∨ p4) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    cases assump_3
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_1
          case intro assump_23 assump_24 =>
            cases assump_24
            case intro assump_27 assump_28 =>
              have assump_127 : (False → p5) := by
                intro assump_34
                apply False.elim assump_34
              let assump_33 := assump_28 assump_127
              apply False.elim assump_33
      case inr assump_12 =>
        cases assump_10
        case intro assump_42 assump_43 =>
          cases assump_1
          case intro assump_50 assump_51 =>
            cases assump_51
            case intro assump_54 assump_55 =>
              have assump_128 : (False → p5) := by
                intro assump_61
                apply False.elim assump_61
              let assump_60 := assump_55 assump_128
              apply False.elim assump_60
  case inr assump_6 =>
    cases assump_3
    case intro assump_69 assump_70 =>
      cases assump_69
      case inl assump_71 =>
        cases assump_70
        case intro assump_75 assump_76 =>
          cases assump_1
          case intro assump_83 assump_84 =>
            cases assump_84
            case intro assump_87 assump_88 =>
              have assump_129 : (False → p5) := by
                intro assump_94
                apply False.elim assump_94
              let assump_93 := assump_88 assump_129
              apply False.elim assump_93
      case inr assump_72 =>
        cases assump_70
        case intro assump_102 assump_103 =>
          cases assump_1
          case intro assump_110 assump_111 =>
            cases assump_111
            case intro assump_114 assump_115 =>
              have assump_130 : (False → p5) := by
                intro assump_121
                apply False.elim assump_121
              let assump_120 := assump_115 assump_130
              apply False.elim assump_120


variable (p0 p1 p6 p4 p7 p2 p3 p5 : Prop)
theorem file45_89399 : (((((p3 → p3) ∧ (True ∨ p0)) → False) ∧ (((p2 ∧ p6) ∧ (p5 → False)) ∧ ((True ∨ False) → (p0 → True)))) → ((((p7 ∧ True) ∧ (p2 ∧ p2)) → ((True ∧ p4) → (p4 ∨ p3))) ∨ (((p1 → p3) ∨ (p0 → False)) → False))) := by
  intro assump_17
  cases assump_17
  case intro assump_18 assump_19 =>
    cases assump_19
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          apply Or.inl
          intro assump_36
          intro assump_37
          cases assump_37
          case intro assump_38 assump_39 =>
            cases assump_36
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_45
                case intro assump_52 assump_53 =>
                  apply Or.inl
                  exact assump_39


variable (p7 p4 p2 p1 p5 p0 p3 : Prop)
theorem file45_90373 : (((((p1 ∨ p0) → False) ∨ ((p4 → p2) ∨ (p1 ∨ p3))) → False) → ((((p7 → p3) → False) ∨ ((False ∧ p0) → (True → False))) → (((False → False) ∧ (p4 ∨ p4)) → ((p5 → p2) → (p5 ∨ True))))) := by
  intro assump_18
  intro assump_19
  intro assump_20
  intro assump_21
  cases assump_20
  case intro assump_24 assump_25 =>
    cases assump_25
    case inl assump_28 =>
      cases assump_19
      case inl assump_32 =>
        apply Or.inr
        apply True.intro
      case inr assump_33 =>
        apply Or.inr
        apply True.intro
    case inr assump_29 =>
      cases assump_19
      case inl assump_44 =>
        apply Or.inr
        apply True.intro
      case inr assump_45 =>
        apply Or.inr
        apply True.intro


variable (p3 p2 p5 p1 p6 p0 p7 p4 : Prop)
theorem file45_91165 : (((((p3 ∧ p2) → (p1 ∧ False)) → ((p0 ∨ p6) → False)) ∧ (((p4 → False) ∧ (True → False)) ∧ ((p1 ∧ False) ∧ (p6 → p6)))) → ((((True ∨ p7) → (p5 ∨ True)) ∧ ((p6 ∨ p6) ∨ (p4 → False))) → (((p4 → False) → (p1 ∧ p1)) → ((p3 ∨ p7) ∨ (True ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_1
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            cases assump_20
            case intro assump_22 assump_23 =>
              cases assump_21
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  apply False.elim assump_31
      case inr assump_13 =>
        cases assump_1
        case intro assump_38 assump_39 =>
          cases assump_39
          case intro assump_42 assump_43 =>
            cases assump_42
            case intro assump_44 assump_45 =>
              cases assump_43
              case intro assump_50 assump_51 =>
                cases assump_50
                case intro assump_52 assump_53 =>
                  apply False.elim assump_53
    case inr assump_11 =>
      cases assump_1
      case intro assump_60 assump_61 =>
        cases assump_61
        case intro assump_64 assump_65 =>
          cases assump_64
          case intro assump_66 assump_67 =>
            cases assump_65
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                apply False.elim assump_75


variable (p1 p4 p0 p2 p7 p3 p6 : Prop)
theorem file45_92947 : (((((p6 ∧ p3) → (p4 → False)) → ((False ∧ p0) → False)) → False) → ((((p0 ∨ p7) → False) → ((p0 ∨ p4) → (True ∨ True))) ∧ (((p0 ∨ True) ∨ (p2 → False)) ∧ ((p1 ∨ p4) → (True ∨ p4))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply Or.inl
    apply True.intro
  case inr assump_5 =>
    apply Or.inl
    apply True.intro
  apply And.intro
  apply Or.inl
  apply Or.inr
  apply True.intro
  intro assump_20
  cases assump_20
  case inl assump_21 =>
    apply Or.inl
    apply True.intro
  case inr assump_22 =>
    apply Or.inl
    apply True.intro


variable (p2 p4 p0 p1 p7 p3 : Prop)
theorem file45_93631 : (((((p4 → False) → False) → ((p4 → False) → (p3 → p3))) → False) → ((((p0 → False) → False) → ((p4 ∧ True) → (True ∧ p7))) → (((p2 ∨ False) → False) ∧ ((p4 ∧ p3) → (False → p1))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    have assump_31 : (((p4 → False) → False) → ((p4 → False) → (p3 → p3))) := by
      intro assump_13
      intro assump_14
      intro assump_15
      exact assump_15
    let assump_12 := assump_1 assump_31
    apply False.elim assump_12
  case inr assump_5 =>
    apply False.elim assump_5
  intro assump_27
  intro assump_28
  apply False.elim assump_28


variable (p3 p0 p2 p7 p1 p6 : Prop)
theorem file45_94345 : (((((p7 → False) → False) → False) ∨ (((p3 → False) ∨ (True ∨ p1)) → False)) → ((((p1 → True) → False) → ((False ∧ p0) → False)) ∨ (((p0 ∧ False) → (p1 → False)) ∨ ((True → p0) ∨ (p6 → p2))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  case inr assump_3 =>
    apply Or.inl
    intro assump_14
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      apply False.elim assump_16


variable (p6 p4 p1 p2 p3 p5 p7 : Prop)
theorem file45_94977 : ((((((p5 → True) ∨ (False ∨ p7)) → False) ∧ (((p4 → False) ∧ (p1 → p1)) ∨ ((p5 ∨ p4) ∨ (p6 → False)))) ∧ ((((p1 → False) ∨ (p3 → False)) ∧ ((p2 ∧ p3) ∨ (p7 → False))) ∧ (((False ∧ p2) → (p7 ∧ p1)) ∧ ((p5 ∨ p5) → (p3 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_19
                case inl assump_24 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    cases assump_17
                    case intro assump_32 assump_33 =>
                      have assump_394 : ((p5 → True) ∨ (False ∨ p7)) := by
                        apply Or.inl
                        intro assump_46
                        apply True.intro
                      let assump_45 := assump_4 assump_394
                      apply False.elim assump_45
                case inr assump_25 =>
                  cases assump_17
                  case intro assump_52 assump_53 =>
                    have assump_395 : ((p5 → True) ∨ (False ∨ p7)) := by
                      apply Or.inl
                      intro assump_65
                      apply True.intro
                    let assump_64 := assump_4 assump_395
                    apply False.elim assump_64
              case inr assump_21 =>
                cases assump_19
                case inl assump_71 =>
                  cases assump_71
                  case intro assump_73 assump_74 =>
                    cases assump_17
                    case intro assump_79 assump_80 =>
                      have assump_396 : p3 := by
                        exact assump_74
                      let assump_89 := assump_21 assump_396
                      apply False.elim assump_89
                case inr assump_72 =>
                  cases assump_17
                  case intro assump_95 assump_96 =>
                    have assump_397 : ((p5 → True) ∨ (False ∨ p7)) := by
                      apply Or.inl
                      intro assump_108
                      apply True.intro
                    let assump_107 := assump_4 assump_397
                    apply False.elim assump_107
      case inr assump_9 =>
        cases assump_9
        case inl assump_112 =>
          cases assump_112
          case inl assump_114 =>
            cases assump_3
            case intro assump_118 assump_119 =>
              cases assump_118
              case intro assump_120 assump_121 =>
                cases assump_120
                case inl assump_122 =>
                  cases assump_121
                  case inl assump_126 =>
                    cases assump_126
                    case intro assump_128 assump_129 =>
                      cases assump_119
                      case intro assump_134 assump_135 =>
                        have assump_398 : (p5 ∨ p5) := by
                          apply Or.inl
                          exact assump_114
                        let assump_140 := assump_135 assump_398
                        have assump_399 : p3 := by
                          exact assump_129
                        let assump_141 := assump_140 assump_399
                        apply False.elim assump_141
                  case inr assump_127 =>
                    cases assump_119
                    case intro assump_147 assump_148 =>
                      have assump_400 : ((p5 → True) ∨ (False ∨ p7)) := by
                        apply Or.inl
                        intro assump_160
                        apply True.intro
                      let assump_159 := assump_4 assump_400
                      apply False.elim assump_159
                case inr assump_123 =>
                  cases assump_121
                  case inl assump_166 =>
                    cases assump_166
                    case intro assump_168 assump_169 =>
                      cases assump_119
                      case intro assump_174 assump_175 =>
                        have assump_401 : (p5 ∨ p5) := by
                          apply Or.inl
                          exact assump_114
                        let assump_180 := assump_175 assump_401
                        have assump_402 : p3 := by
                          exact assump_169
                        let assump_181 := assump_180 assump_402
                        apply False.elim assump_181
                  case inr assump_167 =>
                    cases assump_119
                    case intro assump_187 assump_188 =>
                      have assump_403 : ((p5 → True) ∨ (False ∨ p7)) := by
                        apply Or.inl
                        intro assump_200
                        apply True.intro
                      let assump_199 := assump_4 assump_403
                      apply False.elim assump_199
          case inr assump_115 =>
            cases assump_3
            case intro assump_206 assump_207 =>
              cases assump_206
              case intro assump_208 assump_209 =>
                cases assump_208
                case inl assump_210 =>
                  cases assump_209
                  case inl assump_214 =>
                    cases assump_214
                    case intro assump_216 assump_217 =>
                      cases assump_207
                      case intro assump_222 assump_223 =>
                        have assump_404 : ((p5 → True) ∨ (False ∨ p7)) := by
                          apply Or.inl
                          intro assump_235
                          apply True.intro
                        let assump_234 := assump_4 assump_404
                        apply False.elim assump_234
                  case inr assump_215 =>
                    cases assump_207
                    case intro assump_241 assump_242 =>
                      have assump_405 : ((p5 → True) ∨ (False ∨ p7)) := by
                        apply Or.inl
                        intro assump_253
                        apply True.intro
                      let assump_252 := assump_4 assump_405
                      apply False.elim assump_252
                case inr assump_211 =>
                  cases assump_209
                  case inl assump_259 =>
                    cases assump_259
                    case intro assump_261 assump_262 =>
                      cases assump_207
                      case intro assump_267 assump_268 =>
                        have assump_406 : p3 := by
                          exact assump_262
                        let assump_277 := assump_211 assump_406
                        apply False.elim assump_277
                  case inr assump_260 =>
                    cases assump_207
                    case intro assump_283 assump_284 =>
                      have assump_407 : ((p5 → True) ∨ (False ∨ p7)) := by
                        apply Or.inl
                        intro assump_295
                        apply True.intro
                      let assump_294 := assump_4 assump_407
                      apply False.elim assump_294
        case inr assump_113 =>
          cases assump_3
          case intro assump_301 assump_302 =>
            cases assump_301
            case intro assump_303 assump_304 =>
              cases assump_303
              case inl assump_305 =>
                cases assump_304
                case inl assump_309 =>
                  cases assump_309
                  case intro assump_311 assump_312 =>
                    cases assump_302
                    case intro assump_317 assump_318 =>
                      have assump_408 : ((p5 → True) ∨ (False ∨ p7)) := by
                        apply Or.inl
                        intro assump_330
                        apply True.intro
                      let assump_329 := assump_4 assump_408
                      apply False.elim assump_329
                case inr assump_310 =>
                  cases assump_302
                  case intro assump_336 assump_337 =>
                    have assump_409 : ((p5 → True) ∨ (False ∨ p7)) := by
                      apply Or.inl
                      intro assump_348
                      apply True.intro
                    let assump_347 := assump_4 assump_409
                    apply False.elim assump_347
              case inr assump_306 =>
                cases assump_304
                case inl assump_354 =>
                  cases assump_354
                  case intro assump_356 assump_357 =>
                    cases assump_302
                    case intro assump_362 assump_363 =>
                      have assump_410 : p3 := by
                        exact assump_357
                      let assump_372 := assump_306 assump_410
                      apply False.elim assump_372
                case inr assump_355 =>
                  cases assump_302
                  case intro assump_378 assump_379 =>
                    have assump_411 : ((p5 → True) ∨ (False ∨ p7)) := by
                      apply Or.inl
                      intro assump_390
                      apply True.intro
                    let assump_389 := assump_4 assump_411
                    apply False.elim assump_389


variable (p1 p7 p0 p5 p2 p4 : Prop)
theorem file45_104598 : ((((((p7 ∨ True) ∨ (False → True)) ∨ ((p0 → True) ∨ (False → p5))) ∨ (((p0 ∨ p1) ∧ (True ∧ True)) ∨ ((p2 → p4) ∨ (False ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((p7 ∨ True) ∨ (False → True)) ∨ ((p0 → True) ∨ (False → p5))) ∨ (((p0 ∨ p1) ∧ (True ∧ True)) ∨ ((p2 → p4) ∨ (False ∨ p5)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p1 p0 p3 p6 p5 p2 : Prop)
theorem file45_105132 : ((((((p5 ∨ False) → (p6 → p2)) ∨ ((p0 → p3) ∨ (p1 ∧ p2))) → (((False ∧ p0) → False) ∧ ((p2 → p2) ∨ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p5 ∨ False) → (p6 → p2)) ∨ ((p0 → p3) ∨ (p1 ∧ p2))) → (((False ∧ p0) → False) ∧ ((p2 → p2) ∨ (p6 → False)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
    cases assump_5
    case inl assump_11 =>
      apply Or.inl
      intro assump_15
      exact assump_15
    case inr assump_12 =>
      cases assump_12
      case inl assump_18 =>
        apply Or.inl
        intro assump_22
        exact assump_22
      case inr assump_19 =>
        cases assump_19
        case intro assump_25 assump_26 =>
          apply Or.inl
          intro assump_31
          exact assump_31
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p5 p3 p0 p1 p6 p4 : Prop)
theorem file45_106118 : (((((p6 → p5) → (False → False)) ∨ ((False → False) ∧ (False ∧ p1))) → False) → ((((p0 → p4) ∨ (p6 → p0)) → False) ∧ (((p5 ∧ False) → (True ∨ p1)) ∨ ((p3 ∨ p3) → (False ∨ False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_38 : (((p6 → p5) → (False → False)) ∨ ((False → False) ∧ (False ∧ p1))) := by
      apply Or.inl
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_9 := assump_1 assump_38
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_39 : (((p6 → p5) → (False → False)) ∨ ((False → False) ∧ (False ∧ p1))) := by
      apply Or.inl
      intro assump_22
      intro assump_23
      apply False.elim assump_23
    let assump_21 := assump_1 assump_39
    apply False.elim assump_21
  apply Or.inl
  intro assump_31
  cases assump_31
  case intro assump_32 assump_33 =>
    apply False.elim assump_33


variable (p5 p7 p2 p1 : Prop)
theorem file45_107113 : ((((((p1 ∧ p2) → (p5 → p5)) → ((True ∨ p7) ∨ (p5 → False))) ∨ (((p1 → False) ∧ (p2 → p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p1 ∧ p2) → (p5 → p5)) → ((True ∨ p7) ∨ (p5 → False))) ∨ (((p1 → False) ∧ (p2 → p5)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p6 p7 p3 p4 : Prop)
theorem file45_107590 : (((((False ∧ p3) → (p3 ∧ p4)) ∨ ((True ∧ p5) ∧ (p6 ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_17 : (((False ∧ p3) → (p3 ∧ p4)) ∨ ((True ∧ p5) ∧ (p6 ∨ p7))) := by
    apply Or.inl
    intro assump_5
    apply And.intro
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    cases assump_5
    case intro assump_10 assump_11 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p5 p7 p2 p4 p3 p6 : Prop)
theorem file45_108130 : ((((((p4 ∨ p5) ∧ (True ∧ p7)) ∨ ((p5 → p3) ∧ (p5 ∨ p5))) ∨ (((p7 ∧ p2) → (p7 ∨ p2)) ∧ ((False → False) → (True → p5)))) ∧ ((((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case inl assump_10 =>
            cases assump_9
            case intro assump_14 assump_15 =>
              have assump_114 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
                apply Or.inl
                apply Or.inr
                intro assump_23
                have assump_115 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inr
                  exact assump_23
                let assump_27 := assump_3 assump_115
                apply False.elim assump_27
              let assump_22 := assump_3 assump_114
              apply False.elim assump_22
          case inr assump_11 =>
            cases assump_9
            case intro assump_36 assump_37 =>
              have assump_116 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
                apply Or.inl
                apply Or.inr
                intro assump_45
                have assump_117 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply Or.inr
                  exact assump_45
                let assump_49 := assump_3 assump_117
                apply False.elim assump_49
              let assump_44 := assump_3 assump_116
              apply False.elim assump_44
      case inr assump_7 =>
        cases assump_7
        case intro assump_56 assump_57 =>
          cases assump_57
          case inl assump_60 =>
            have assump_118 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_67
              have assump_119 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_67
              let assump_71 := assump_3 assump_119
              apply False.elim assump_71
            let assump_66 := assump_3 assump_118
            apply False.elim assump_66
          case inr assump_61 =>
            have assump_120 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
              apply Or.inl
              apply Or.inr
              intro assump_83
              have assump_121 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
                apply Or.inl
                apply Or.inl
                apply Or.inr
                exact assump_83
              let assump_87 := assump_3 assump_121
              apply False.elim assump_87
            let assump_82 := assump_3 assump_120
            apply False.elim assump_82
    case inr assump_5 =>
      cases assump_5
      case intro assump_94 assump_95 =>
        have assump_122 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
          apply Or.inl
          apply Or.inr
          intro assump_103
          have assump_123 : (((p2 ∨ p6) ∨ (p6 → False)) ∨ ((p5 → False) → False)) := by
            apply Or.inl
            apply Or.inl
            apply Or.inr
            exact assump_103
          let assump_107 := assump_3 assump_123
          apply False.elim assump_107
        let assump_102 := assump_3 assump_122
        apply False.elim assump_102


variable (p3 p5 p2 p1 p7 p4 : Prop)
theorem file45_111949 : (((((p2 ∨ p7) → False) ∧ ((False → False) ∧ (p5 → False))) → False) → ((((p4 ∨ p2) → (p3 ∧ True)) ∧ ((p2 ∧ p2) → (p1 → False))) → (((False ∧ p5) → False) ∨ ((True ∧ p2) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      apply False.elim assump_12


variable (p2 p0 p5 p6 p7 p4 p1 p3 : Prop)
theorem file45_112415 : (((((False ∨ False) → False) ∨ ((p1 ∨ p0) ∧ (False → False))) ∨ (((p0 → p6) → False) ∨ ((p5 → False) ∨ (p1 ∧ p6)))) ∨ ((((p5 → False) ∨ (p4 ∧ p1)) ∨ ((p7 → False) ∧ (p2 → p2))) ∨ (((p6 ∨ False) ∨ (p3 ∧ p6)) ∧ ((p7 ∧ p4) → (p3 ∧ p7))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply False.elim assump_2
  case inr assump_3 =>
    apply False.elim assump_3


variable (p2 p6 p3 p7 p5 p0 : Prop)
theorem file45_112902 : (((((False ∨ p2) → (p0 ∨ p2)) → False) → (((False → False) ∨ (False ∧ p5)) → ((p0 → False) → (p7 ∨ True)))) ∨ ((((p2 → p5) → False) ∧ ((p7 → p0) ∧ (p6 ∧ p0))) ∨ (((p3 → False) ∨ (p5 → True)) → ((p2 ∧ p7) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    apply Or.inr
    apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_12 assump_13 =>
      apply False.elim assump_12


variable (p7 p0 p4 p6 p2 : Prop)
theorem file45_113445 : (((((p2 → False) ∧ (True → False)) → False) → False) → ((((p2 ∧ True) → (p4 → p4)) → ((p2 → False) ∧ (p4 ∨ False))) → (((p2 ∧ p0) ∨ (False → True)) ∧ ((p2 ∧ p7) ∧ (p6 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply Or.inr
  intro assump_7
  apply True.intro
  apply And.intro
  apply And.intro
  have assump_68 : (((p2 → False) ∧ (True → False)) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      have assump_69 : True := by
        apply True.intro
      let assump_20 := assump_15 assump_69
      apply False.elim assump_20
  let assump_12 := assump_1 assump_68
  apply False.elim assump_12
  have assump_70 : (((p2 → False) ∧ (True → False)) → False) := by
    intro assump_32
    cases assump_32
    case intro assump_33 assump_34 =>
      have assump_71 : True := by
        apply True.intro
      let assump_39 := assump_34 assump_71
      apply False.elim assump_39
  let assump_31 := assump_1 assump_70
  apply False.elim assump_31
  intro assump_46
  have assump_72 : (((p2 → False) ∧ (True → False)) → False) := by
    intro assump_54
    cases assump_54
    case intro assump_55 assump_56 =>
      have assump_73 : True := by
        apply True.intro
      let assump_61 := assump_56 assump_73
      apply False.elim assump_61
  let assump_53 := assump_1 assump_72
  apply False.elim assump_53


variable (p5 p0 p7 p4 p2 p6 : Prop)
theorem file45_114889 : (((((False ∨ p7) ∨ (p2 ∨ p7)) → False) ∧ (((False ∧ True) ∧ (False → p0)) → False)) → ((((True ∨ p6) ∧ (p5 → False)) ∧ ((p7 ∨ True) ∨ (p5 → False))) → (((False ∧ p2) → (p0 → False)) ∨ ((False ∧ p4) ∧ (True → True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_4
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_1
            case intro assump_19 assump_20 =>
              apply Or.inl
              intro assump_25
              intro assump_26
              cases assump_25
              case intro assump_29 assump_30 =>
                apply False.elim assump_29
          case inr assump_16 =>
            cases assump_1
            case intro assump_35 assump_36 =>
              apply Or.inl
              intro assump_41
              intro assump_42
              cases assump_41
              case intro assump_45 assump_46 =>
                apply False.elim assump_45
        case inr assump_14 =>
          cases assump_1
          case intro assump_51 assump_52 =>
            apply Or.inl
            intro assump_57
            intro assump_58
            cases assump_57
            case intro assump_61 assump_62 =>
              apply False.elim assump_61
      case inr assump_8 =>
        cases assump_4
        case inl assump_69 =>
          cases assump_69
          case inl assump_71 =>
            cases assump_1
            case intro assump_75 assump_76 =>
              apply Or.inl
              intro assump_81
              intro assump_82
              cases assump_81
              case intro assump_85 assump_86 =>
                apply False.elim assump_85
          case inr assump_72 =>
            cases assump_1
            case intro assump_91 assump_92 =>
              apply Or.inl
              intro assump_97
              intro assump_98
              cases assump_97
              case intro assump_101 assump_102 =>
                apply False.elim assump_101
        case inr assump_70 =>
          cases assump_1
          case intro assump_107 assump_108 =>
            apply Or.inl
            intro assump_113
            intro assump_114
            cases assump_113
            case intro assump_117 assump_118 =>
              apply False.elim assump_117


variable (p5 p1 p3 p2 p4 : Prop)
theorem file45_117396 : ((((((p5 ∨ False) ∨ (p1 → False)) ∨ ((p4 → False) ∧ (p3 ∧ p4))) → (((p3 → False) ∨ (p3 → p2)) → ((p4 ∨ p3) ∨ (p5 → p5)))) ∧ ((((True → False) ∧ (False ∨ False)) → ((p5 → False) ∨ (p3 ∨ p1))) → False)) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    have assump_31 : (((True → False) ∧ (False ∨ False)) → ((p5 → False) ∨ (p3 ∨ p1))) := by
      intro assump_17
      cases assump_17
      case intro assump_18 assump_19 =>
        cases assump_19
        case inl assump_22 =>
          apply False.elim assump_22
        case inr assump_23 =>
          apply False.elim assump_23
    let assump_16 := assump_11 assump_31
    apply False.elim assump_16


variable (p3 p0 p2 p5 p4 p6 p1 p7 : Prop)
theorem file45_118155 : (((((True → True) → False) → ((p5 → p2) → (p6 ∧ False))) ∨ (((p1 ∧ p0) ∧ (p5 ∨ p5)) ∧ ((p1 → False) ∧ (p6 ∨ p7)))) ∨ ((((p7 ∧ p3) → False) ∧ ((p4 → p3) → False)) ∧ (((p0 ∨ p6) ∨ (False ∨ p5)) → ((p1 ∧ p2) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_9
  intro assump_10
  apply And.intro
  have assump_29 : (True → True) := by
    intro assump_16
    apply True.intro
  let assump_15 := assump_9 assump_29
  apply False.elim assump_15
  have assump_30 : (True → True) := by
    intro assump_25
    apply True.intro
  let assump_24 := assump_9 assump_30
  apply False.elim assump_24


variable (p4 p6 p2 p3 p5 p7 : Prop)
theorem file45_118815 : ((((((False ∧ True) → False) ∨ ((p4 → p3) ∨ (p7 ∧ p4))) ∨ (((p5 → False) ∧ (p2 ∧ p6)) ∧ ((p4 → p4) ∧ (p3 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ True) → False) ∨ ((p4 → p3) ∨ (p7 ∧ p4))) ∨ (((p5 → False) ∧ (p2 ∧ p6)) ∧ ((p4 → p4) ∧ (p3 ∨ p5)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p2 p7 p5 p0 p1 : Prop)
theorem file45_119372 : ((((((p2 → p6) → False) ∧ ((p0 ∧ p7) → False)) → False) ∧ ((((p6 ∨ p7) → (p5 ∧ True)) ∨ ((p0 ∨ p1) ∧ (p5 → False))) ∧ (((p2 ∧ p1) ∧ (p0 → False)) ∧ ((False ∧ False) ∧ (p2 → p0))))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_11
    case intro assump_14 assump_15 =>
      cases assump_14
      case inl assump_16 =>
        cases assump_15
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              cases assump_21
              case intro assump_32 assump_33 =>
                cases assump_32
                case intro assump_34 assump_35 =>
                  apply False.elim assump_34
      case inr assump_17 =>
        cases assump_17
        case intro assump_38 assump_39 =>
          cases assump_38
          case inl assump_40 =>
            cases assump_15
            case intro assump_46 assump_47 =>
              cases assump_46
              case intro assump_48 assump_49 =>
                cases assump_48
                case intro assump_50 assump_51 =>
                  cases assump_47
                  case intro assump_58 assump_59 =>
                    cases assump_58
                    case intro assump_60 assump_61 =>
                      apply False.elim assump_60
          case inr assump_41 =>
            cases assump_15
            case intro assump_68 assump_69 =>
              cases assump_68
              case intro assump_70 assump_71 =>
                cases assump_70
                case intro assump_72 assump_73 =>
                  cases assump_69
                  case intro assump_80 assump_81 =>
                    cases assump_80
                    case intro assump_82 assump_83 =>
                      apply False.elim assump_82


variable (p3 p0 p4 p1 : Prop)
theorem file45_121317 : (((((p0 ∧ True) → (p3 ∧ True)) ∨ ((p1 → p1) → False)) ∧ (((p3 → p3) ∧ (False → False)) ∧ ((True ∨ p4) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_38 : (True ∨ p4) := by
            apply Or.inl
            apply True.intro
          let assump_18 := assump_9 assump_38
          apply False.elim assump_18
    case inr assump_5 =>
      cases assump_3
      case intro assump_24 assump_25 =>
        cases assump_24
        case intro assump_26 assump_27 =>
          have assump_39 : (True ∨ p4) := by
            apply Or.inl
            apply True.intro
          let assump_34 := assump_25 assump_39
          apply False.elim assump_34


variable (p1 p7 p2 : Prop)
theorem file45_122249 : (((((True ∧ p1) ∨ (True ∨ False)) → False) → False) ∨ ((((p7 ∧ p2) ∧ (p7 ∧ p1)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  have assump_8 : ((True ∧ p1) ∨ (True ∨ False)) := by
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p5 p4 p6 p3 p0 p7 : Prop)
theorem file45_122620 : ((((((p6 ∧ p0) ∨ (False → False)) → False) → (((p5 ∧ p3) → (p4 → False)) ∨ ((p7 → False) → (True ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_31 : ((((p6 ∧ p0) ∨ (False → False)) → False) → (((p5 ∧ p3) → (p4 → False)) ∨ ((p7 → False) → (True ∧ p4)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    cases assump_8
    case intro assump_12 assump_13 =>
      have assump_32 : ((p6 ∧ p0) ∨ (False → False)) := by
        apply Or.inr
        intro assump_22
        apply False.elim assump_22
      let assump_21 := assump_5 assump_32
      apply False.elim assump_21
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4


variable (p4 p7 p0 p1 p3 p2 : Prop)
theorem file45_123366 : (((((p2 → False) ∨ (p7 ∨ p1)) → ((True → False) ∧ (p4 ∨ p3))) ∧ (((True → False) → (p7 → p0)) → False)) → ((((True → False) ∨ (False → False)) → ((p4 → p4) → (p1 → p1))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_25 : ((True → False) → (p7 → p0)) := by
      intro assump_12
      intro assump_13
      have assump_26 : True := by
        apply True.intro
      let assump_18 := assump_12 assump_26
      apply False.elim assump_18
    let assump_11 := assump_6 assump_25
    apply False.elim assump_11


variable (p5 p2 p4 p7 p0 p1 : Prop)
theorem file45_124003 : ((((((p0 → False) ∨ (p2 → p5)) ∨ ((p1 ∨ p4) → False)) → (((True → False) → (p5 ∧ True)) ∨ ((p7 ∧ False) → False))) → False) → False) := by
  intro assump_1
  have assump_40 : ((((p0 → False) ∨ (p2 → p5)) ∨ ((p1 ∨ p4) → False)) → (((True → False) → (p5 ∧ True)) ∨ ((p7 ∧ False) → False))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_12
        apply And.intro
        have assump_41 : True := by
          apply True.intro
        let assump_15 := assump_12 assump_41
        apply False.elim assump_15
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        intro assump_21
        apply And.intro
        have assump_42 : True := by
          apply True.intro
        let assump_24 := assump_21 assump_42
        apply False.elim assump_24
        apply True.intro
    case inr assump_7 =>
      apply Or.inl
      intro assump_30
      apply And.intro
      have assump_43 : True := by
        apply True.intro
      let assump_33 := assump_30 assump_43
      apply False.elim assump_33
      apply True.intro
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p4 p6 p3 p5 p1 p7 p0 : Prop)
theorem file45_125283 : (((((p4 → False) → False) → False) ∧ (((False → True) → (True ∨ p7)) → False)) → ((((p4 ∧ p0) → (p1 → p5)) ∨ ((p3 → p1) ∧ (p6 → False))) → (((p4 → False) → False) ∨ ((p7 → False) → (p1 ∨ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      apply Or.inl
      intro assump_13
      have assump_47 : ((False → True) → (True ∨ p7)) := by
        intro assump_18
        apply Or.inl
        apply True.intro
      let assump_17 := assump_8 assump_47
      apply False.elim assump_17
  case inr assump_4 =>
    cases assump_4
    case intro assump_24 assump_25 =>
      cases assump_1
      case intro assump_30 assump_31 =>
        apply Or.inl
        intro assump_36
        have assump_48 : ((False → True) → (True ∨ p7)) := by
          intro assump_41
          apply Or.inl
          apply True.intro
        let assump_40 := assump_31 assump_48
        apply False.elim assump_40


variable (p4 p5 p0 p6 p1 p2 p7 p3 : Prop)
theorem file45_126329 : (((((p2 → p1) → (p0 → False)) → ((p7 ∨ p3) ∧ (False → p5))) ∧ (((p6 ∧ p3) → (p6 → True)) → False)) → ((((p5 ∧ p4) ∧ (p2 → True)) ∨ ((p6 → False) → (p7 → p7))) → False)) := by
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
          have assump_41 : ((p6 ∧ p3) → (p6 → True)) := by
            intro assump_22
            intro assump_23
            apply True.intro
          let assump_21 := assump_16 assump_41
          apply False.elim assump_21
  case inr assump_4 =>
    cases assump_1
    case intro assump_29 assump_30 =>
      have assump_42 : ((p6 ∧ p3) → (p6 → True)) := by
        intro assump_36
        intro assump_37
        apply True.intro
      let assump_35 := assump_30 assump_42
      apply False.elim assump_35


variable (p6 p7 p5 p3 p0 p4 : Prop)
theorem file45_127329 : (((((p4 → p6) → (p7 ∨ True)) → False) ∧ (((p0 ∨ p3) ∨ (p6 → False)) ∨ ((p0 ∧ p5) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_52 : ((p4 → p6) → (p7 ∨ True)) := by
            intro assump_16
            apply Or.inr
            apply True.intro
          let assump_15 := assump_2 assump_52
          apply False.elim assump_15
        case inr assump_11 =>
          have assump_53 : ((p4 → p6) → (p7 ∨ True)) := by
            intro assump_26
            apply Or.inr
            apply True.intro
          let assump_25 := assump_2 assump_53
          apply False.elim assump_25
      case inr assump_9 =>
        have assump_54 : ((p4 → p6) → (p7 ∨ True)) := by
          intro assump_36
          apply Or.inr
          apply True.intro
        let assump_35 := assump_2 assump_54
        apply False.elim assump_35
    case inr assump_7 =>
      have assump_55 : ((p4 → p6) → (p7 ∨ True)) := by
        intro assump_46
        apply Or.inr
        apply True.intro
      let assump_45 := assump_2 assump_55
      apply False.elim assump_45


