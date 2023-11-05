variable (p7 p3 p4 p1 p5 : Prop)
theorem file67_41 : (((((p4 ∧ p5) → False) ∧ ((p4 → False) ∨ (p1 ∧ p7))) ∧ (((True → False) → (p4 ∨ p5)) → False)) → ((((False → False) ∨ (True → False)) → ((p7 ∧ False) ∨ (p4 ∧ p5))) → (((p3 → False) → (False → False)) → ((False ∨ False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply False.elim assump_5
  case inr assump_6 =>
    apply False.elim assump_6


variable (p2 p0 p7 p3 p4 p5 p1 : Prop)
theorem file67_532 : (((((True → False) → False) → ((p5 ∨ True) ∨ (p3 → p5))) ∨ (((p2 → False) → False) → ((p5 → False) → (p1 → False)))) ∨ ((((p2 ∧ p1) → False) ∨ ((p7 ∨ p7) ∨ (p1 → False))) ∧ (((p7 ∧ p1) ∨ (p0 ∧ p1)) ∧ ((p4 → p4) → (p4 ∧ True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply True.intro


variable (p1 p5 p4 p6 p2 p7 : Prop)
theorem file67_923 : ((((((p2 ∧ p2) ∧ (p1 ∨ False)) → False) → (((p5 ∨ p7) ∨ (p6 → p4)) → ((False ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p2 ∧ p2) ∧ (p1 ∨ False)) → False) → (((p5 ∨ p7) ∨ (p6 → p4)) → ((False ∧ p1) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p6 p5 p1 p2 p7 p3 : Prop)
theorem file67_1444 : ((((((p6 ∧ False) ∧ (p1 → False)) → False) → (((p7 ∧ p2) ∨ (p7 ∨ p1)) → ((p6 → False) ∨ (p5 ∧ p3)))) ∧ ((((p7 ∨ p5) → (False → False)) ∨ ((False → False) ∨ (p6 ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p7 ∨ p5) → (False → False)) ∨ ((False → False) ∨ (p6 ∧ False))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p4 p1 p0 p5 p6 p2 : Prop)
theorem file67_2026 : (((((p4 ∨ False) ∧ (p2 ∧ False)) ∧ ((p0 ∨ p6) ∧ (p2 ∨ False))) ∧ (((p1 ∧ p2) → False) → False)) → ((((p5 ∨ True) ∧ (p5 ∧ p1)) → ((p0 → False) ∧ (True → False))) ∨ (((p2 → p6) ∧ (p5 ∨ p2)) ∧ ((p5 → p5) → (p1 → False))))) := by
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
          case intro assump_12 assump_13 =>
            apply False.elim assump_13
        case inr assump_9 =>
          apply False.elim assump_9


variable (p6 p3 p1 p7 p2 p4 p0 : Prop)
theorem file67_2722 : ((((((p6 ∧ p4) → False) ∨ ((p1 ∧ False) → (p6 ∨ p7))) ∧ (((p3 → p7) ∨ (p1 → False)) ∨ ((p7 → p6) ∧ (p7 → False)))) ∧ ((((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            have assump_136 : (((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) := by
              apply Or.inl
              intro assump_19
              intro assump_20
              cases assump_19
              case intro assump_23 assump_24 =>
                apply False.elim assump_24
            let assump_18 := assump_3 assump_136
            apply False.elim assump_18
          case inr assump_13 =>
            have assump_137 : (((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) := by
              apply Or.inl
              intro assump_37
              intro assump_38
              cases assump_37
              case intro assump_41 assump_42 =>
                apply False.elim assump_42
            let assump_36 := assump_3 assump_137
            apply False.elim assump_36
        case inr assump_11 =>
          cases assump_11
          case intro assump_50 assump_51 =>
            have assump_138 : (((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) := by
              apply Or.inl
              intro assump_59
              intro assump_60
              cases assump_59
              case intro assump_63 assump_64 =>
                apply False.elim assump_64
            let assump_58 := assump_3 assump_138
            apply False.elim assump_58
      case inr assump_7 =>
        cases assump_5
        case inl assump_74 =>
          cases assump_74
          case inl assump_76 =>
            have assump_139 : (((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) := by
              apply Or.inl
              intro assump_83
              intro assump_84
              cases assump_83
              case intro assump_87 assump_88 =>
                apply False.elim assump_88
            let assump_82 := assump_3 assump_139
            apply False.elim assump_82
          case inr assump_77 =>
            have assump_140 : (((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) := by
              apply Or.inl
              intro assump_101
              intro assump_102
              cases assump_101
              case intro assump_105 assump_106 =>
                apply False.elim assump_106
            let assump_100 := assump_3 assump_140
            apply False.elim assump_100
        case inr assump_75 =>
          cases assump_75
          case intro assump_114 assump_115 =>
            have assump_141 : (((p0 ∧ False) → (p4 → False)) ∨ ((p6 ∨ p2) → False)) := by
              apply Or.inl
              intro assump_123
              intro assump_124
              cases assump_123
              case intro assump_127 assump_128 =>
                apply False.elim assump_128
            let assump_122 := assump_3 assump_141
            apply False.elim assump_122


variable (p6 p1 p2 : Prop)
theorem file67_5988 : (((((p1 ∨ p6) ∨ (p6 → False)) ∨ ((p6 ∧ p2) ∨ (p1 → False))) → False) → False) := by
  intro assump_15
  have assump_30 : (((p1 ∨ p6) ∨ (p6 → False)) ∨ ((p6 ∧ p2) ∨ (p1 → False))) := by
    apply Or.inl
    apply Or.inr
    intro assump_19
    have assump_31 : (((p1 ∨ p6) ∨ (p6 → False)) ∨ ((p6 ∧ p2) ∨ (p1 → False))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inr
      exact assump_19
    let assump_23 := assump_15 assump_31
    apply False.elim assump_23
  let assump_18 := assump_15 assump_30
  apply False.elim assump_18


variable (p1 p5 p6 p7 p2 p4 p0 : Prop)
theorem file67_6594 : (((((p6 → False) ∧ (p6 ∧ p0)) → ((p6 → False) → False)) ∨ (((True → False) ∧ (p4 → False)) ∧ ((p6 → False) → (p6 → False)))) ∧ ((((p5 → p2) ∨ (p4 ∨ p6)) ∧ ((True ∨ p7) → False)) → (((p1 → False) ∧ (p1 → p7)) ∨ ((p6 → True) → False)))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_88 : p6 := by
        exact assump_9
      let assump_17 := assump_5 assump_88
      apply False.elim assump_17
  intro assump_21
  cases assump_21
  case intro assump_22 assump_23 =>
    cases assump_22
    case inl assump_24 =>
      apply Or.inl
      apply And.intro
      intro assump_30
      have assump_89 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_34 := assump_23 assump_89
      apply False.elim assump_34
      intro assump_38
      have assump_90 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_42 := assump_23 assump_90
      apply False.elim assump_42
    case inr assump_25 =>
      cases assump_25
      case inl assump_46 =>
        apply Or.inl
        apply And.intro
        intro assump_52
        have assump_91 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_56 := assump_23 assump_91
        apply False.elim assump_56
        intro assump_60
        have assump_92 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_64 := assump_23 assump_92
        apply False.elim assump_64
      case inr assump_47 =>
        apply Or.inl
        apply And.intro
        intro assump_72
        have assump_93 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_76 := assump_23 assump_93
        apply False.elim assump_76
        intro assump_80
        have assump_94 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_84 := assump_23 assump_94
        apply False.elim assump_84


variable (p4 p1 p2 p0 p6 p3 : Prop)
theorem file67_8710 : (((((p1 ∧ p2) ∨ (p2 ∨ p6)) → False) → (((False → False) → False) → False)) ∨ ((((False ∧ p1) → False) ∧ ((p3 ∧ p3) ∧ (p0 ∧ p2))) ∨ (((p4 ∧ False) ∨ (True ∧ p2)) ∨ ((p6 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  have assump_15 : (False → False) := by
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_2 assump_15
  apply False.elim assump_8


variable (p3 p0 p4 p1 p6 p2 p7 : Prop)
theorem file67_9172 : ((((((p3 → False) → (p3 → False)) → ((p3 → False) ∧ (True ∧ p7))) ∧ (((p2 ∨ p7) → (False → False)) → False)) ∧ ((((p7 ∨ p6) ∧ (p6 ∨ p2)) ∧ ((p4 ∨ p1) → (p0 ∧ p1))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_21 : ((p2 ∨ p7) → (False → False)) := by
        intro assump_14
        intro assump_15
        apply False.elim assump_15
      let assump_13 := assump_5 assump_21
      apply False.elim assump_13


variable (p4 p2 p1 p3 p5 p6 p0 p7 : Prop)
theorem file67_9767 : (((((True ∨ p4) → (p2 ∧ False)) ∧ ((p5 ∧ p5) → (p0 ∧ p5))) → (((p7 → p6) ∨ (p1 ∨ p0)) ∧ ((p3 ∧ p4) → False))) ∨ ((((p5 → False) → (p4 ∧ p0)) ∨ ((p4 → False) ∨ (p5 ∧ False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    intro assump_8
    have assump_39 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_13 := assump_2 assump_39
    let assump_14 := And.right assump_13
    apply False.elim assump_14
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      have assump_40 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_33 := assump_26 assump_40
      let assump_34 := And.right assump_33
      apply False.elim assump_34


variable (p5 : Prop)
theorem file67_10667 : ((((((True → False) → (False → p5)) ∧ ((p5 → False) ∧ (p5 ∨ False))) → False) → False) → False) := by
  intro assump_1
  have assump_28 : ((((True → False) → (False → p5)) ∧ ((p5 → False) ∧ (p5 ∨ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case inl assump_14 =>
          have assump_29 : p5 := by
            exact assump_14
          let assump_19 := assump_10 assump_29
          apply False.elim assump_19
        case inr assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p3 p6 p0 p4 p7 p2 : Prop)
theorem file67_11416 : ((((((False ∨ False) ∨ (p7 ∧ p6)) → ((p3 ∨ p2) → (p6 ∨ False))) ∨ (((p6 ∨ True) → (p0 → False)) ∨ ((p2 → False) ∧ (p3 ∧ p4)))) → False) → False) := by
  intro assump_1
  have assump_44 : ((((False ∨ False) ∨ (p7 ∧ p6)) → ((p3 ∨ p2) → (p6 ∨ False))) ∨ (((p6 ∨ True) → (p0 → False)) ∨ ((p2 → False) ∧ (p3 ∧ p4)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case inl assump_11 =>
        cases assump_11
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          apply False.elim assump_14
      case inr assump_12 =>
        cases assump_12
        case intro assump_19 assump_20 =>
          apply Or.inl
          exact assump_20
    case inr assump_8 =>
      cases assump_5
      case inl assump_27 =>
        cases assump_27
        case inl assump_29 =>
          apply False.elim assump_29
        case inr assump_30 =>
          apply False.elim assump_30
      case inr assump_28 =>
        cases assump_28
        case intro assump_35 assump_36 =>
          apply Or.inl
          exact assump_36
  let assump_4 := assump_1 assump_44
  apply False.elim assump_4


variable (p5 p0 p6 p2 p3 p1 p4 : Prop)
theorem file67_12686 : (((((p1 → p2) → False) → False) ∨ (((False → False) ∨ (p4 → False)) ∧ ((p6 → False) → (p2 ∨ True)))) → ((((p1 ∨ p6) ∧ (p3 ∧ False)) → ((True → False) → (p4 ∨ p5))) ∨ (((p2 → False) ∧ (p5 ∨ p0)) ∨ ((p2 ∨ p4) → False)))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        cases assump_11
        case intro assump_16 assump_17 =>
          apply False.elim assump_17
      case inr assump_13 =>
        cases assump_11
        case intro assump_24 assump_25 =>
          apply False.elim assump_25
  case inr assump_3 =>
    cases assump_3
    case intro assump_30 assump_31 =>
      cases assump_30
      case inl assump_32 =>
        apply Or.inl
        intro assump_38
        intro assump_39
        cases assump_38
        case intro assump_42 assump_43 =>
          cases assump_42
          case inl assump_44 =>
            cases assump_43
            case intro assump_48 assump_49 =>
              apply False.elim assump_49
          case inr assump_45 =>
            cases assump_43
            case intro assump_56 assump_57 =>
              apply False.elim assump_57
      case inr assump_33 =>
        apply Or.inl
        intro assump_66
        intro assump_67
        cases assump_66
        case intro assump_70 assump_71 =>
          cases assump_70
          case inl assump_72 =>
            cases assump_71
            case intro assump_76 assump_77 =>
              apply False.elim assump_77
          case inr assump_73 =>
            cases assump_71
            case intro assump_84 assump_85 =>
              apply False.elim assump_85


variable (p0 p6 p1 p4 p5 p2 p7 : Prop)
theorem file67_14495 : ((((((p7 → True) ∧ (p4 → True)) ∨ ((True → False) → (p2 ∧ p1))) ∧ (((p0 ∨ p2) → (p5 → False)) → False)) ∧ ((((p1 ∧ p4) ∨ (True ∨ p5)) → False) ∧ (((p5 → p0) ∨ (False ∧ True)) ∧ ((True → p1) ∨ (p6 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case intro assump_20 assump_21 =>
              cases assump_20
              case inl assump_22 =>
                cases assump_21
                case inl assump_26 =>
                  have assump_82 : ((p1 ∧ p4) ∨ (True ∨ p5)) := by
                    apply Or.inr
                    apply Or.inl
                    apply True.intro
                  let assump_33 := assump_16 assump_82
                  apply False.elim assump_33
                case inr assump_27 =>
                  cases assump_27
                  case intro assump_37 assump_38 =>
                    apply False.elim assump_38
              case inr assump_23 =>
                cases assump_23
                case intro assump_43 assump_44 =>
                  apply False.elim assump_43
      case inr assump_7 =>
        cases assump_3
        case intro assump_51 assump_52 =>
          cases assump_52
          case intro assump_55 assump_56 =>
            cases assump_55
            case inl assump_57 =>
              cases assump_56
              case inl assump_61 =>
                have assump_83 : ((p1 ∧ p4) ∨ (True ∨ p5)) := by
                  apply Or.inr
                  apply Or.inl
                  apply True.intro
                let assump_68 := assump_51 assump_83
                apply False.elim assump_68
              case inr assump_62 =>
                cases assump_62
                case intro assump_72 assump_73 =>
                  apply False.elim assump_73
            case inr assump_58 =>
              cases assump_58
              case intro assump_78 assump_79 =>
                apply False.elim assump_78


variable (p5 p7 p6 p0 p3 : Prop)
theorem file67_16759 : ((((((True → p6) → False) ∧ ((p7 ∧ p5) → False)) → (((p6 → False) → (p6 → p7)) ∨ ((p0 ∨ p3) → False))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → p6) → False) ∧ ((p7 ∧ p5) → False)) → (((p6 → False) → (p6 → p7)) ∨ ((p0 ∨ p3) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      intro assump_13
      have assump_26 : p6 := by
        exact assump_13
      let assump_18 := assump_12 assump_26
      apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p6 p2 p0 : Prop)
theorem file67_17417 : (((((False ∧ p2) → False) → ((False → False) → False)) → False) ∨ ((((True ∨ True) → (p0 → False)) → False) ∨ (((p3 ∧ True) → (p3 → p0)) ∨ ((p3 → False) ∨ (p6 ∨ False))))) := by
  apply Or.inl
  intro assump_1
  have assump_17 : ((False ∧ p2) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_17
  have assump_18 : (False → False) := by
    intro assump_11
    apply False.elim assump_11
  let assump_10 := assump_4 assump_18
  apply False.elim assump_10


variable (p6 p3 p2 p5 p7 p4 p0 p1 : Prop)
theorem file67_18043 : (((((True ∨ p1) ∧ (p1 ∨ True)) → ((False → False) ∨ (p4 ∧ p6))) → (((p6 ∧ True) ∨ (p4 → True)) ∨ ((False → p7) ∨ (p5 → p1)))) ∨ ((((p1 ∨ p0) ∨ (p3 ∧ p2)) → ((True ∧ True) → False)) ∧ (((p7 → p2) → False) ∧ ((p5 ∧ True) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_34
  apply Or.inl
  apply Or.inr
  intro assump_37
  apply True.intro


variable (p1 p7 p2 p5 : Prop)
theorem file67_18441 : ((((((False ∧ p7) → (p1 ∧ p7)) → False) → (((p2 ∧ True) ∨ (p5 ∨ p2)) → False)) → False) → False) := by
  intro assump_1
  have assump_69 : ((((False ∧ p7) → (p1 ∧ p7)) → False) → (((p2 ∧ True) ∨ (p5 ∨ p2)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_70 : ((False ∧ p7) → (p1 ∧ p7)) := by
          intro assump_18
          apply And.intro
          cases assump_18
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
          cases assump_18
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
        let assump_17 := assump_5 assump_70
        apply False.elim assump_17
    case inr assump_8 =>
      cases assump_8
      case inl assump_30 =>
        have assump_71 : ((False ∧ p7) → (p1 ∧ p7)) := by
          intro assump_37
          apply And.intro
          cases assump_37
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
          cases assump_37
          case intro assump_42 assump_43 =>
            apply False.elim assump_42
        let assump_36 := assump_5 assump_71
        apply False.elim assump_36
      case inr assump_31 =>
        have assump_72 : ((False ∧ p7) → (p1 ∧ p7)) := by
          intro assump_54
          apply And.intro
          cases assump_54
          case intro assump_55 assump_56 =>
            apply False.elim assump_55
          cases assump_54
          case intro assump_59 assump_60 =>
            apply False.elim assump_59
        let assump_53 := assump_5 assump_72
        apply False.elim assump_53
  let assump_4 := assump_1 assump_69
  apply False.elim assump_4


variable (p2 p1 p5 p6 p0 p3 p4 : Prop)
theorem file67_20256 : (((((False ∧ p0) ∧ (p0 ∨ p6)) ∨ ((p1 ∧ p4) → False)) → (((p2 → False) → (p2 → p5)) ∧ ((False ∨ p2) ∨ (True ∨ p1)))) ∨ ((((p2 ∨ p5) → False) → ((p3 → p2) → (p5 → False))) ∨ (((p4 ∨ p1) ∧ (p3 → False)) ∧ ((p2 → False) ∨ (p6 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case inl assump_8 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        apply False.elim assump_12
  case inr assump_9 =>
    have assump_33 : p2 := by
      exact assump_3
    let assump_19 := assump_2 assump_33
    apply False.elim assump_19
  cases assump_1
  case inl assump_23 =>
    cases assump_23
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        apply False.elim assump_27
  case inr assump_24 =>
    apply Or.inr
    apply Or.inl
    apply True.intro


variable (p0 p7 : Prop)
theorem file67_21242 : ((((((p0 ∨ True) ∧ (p7 → p7)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((p0 ∨ True) ∧ (p7 → p7)) → False) → False) := by
    intro assump_5
    have assump_19 : ((p0 ∨ True) ∧ (p7 → p7)) := by
      apply And.intro
      apply Or.inr
      apply True.intro
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p6 p0 p2 p1 p5 : Prop)
theorem file67_21774 : (((((False ∧ p5) ∧ (p4 ∧ True)) → ((p5 ∨ p2) → False)) ∨ (((p0 → False) ∧ (p4 ∧ False)) → ((p1 → False) ∨ (True → False)))) ∨ ((((p6 ∨ p2) → False) → ((True → False) → False)) ∧ (((p5 → False) ∧ (False ∨ p4)) → ((True → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        apply False.elim assump_9
  case inr assump_4 =>
    cases assump_1
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        apply False.elim assump_17


variable (p6 p3 p0 p2 : Prop)
theorem file67_22503 : (((((p6 → p0) ∧ (p2 → p0)) ∧ ((False → False) ∧ (False ∧ True))) ∧ (((p3 → p6) → False) → ((p2 → False) → False))) → False) := by
  intro assump_26
  cases assump_26
  case intro assump_27 assump_28 =>
    cases assump_27
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_30
        case intro assump_37 assump_38 =>
          cases assump_38
          case intro assump_41 assump_42 =>
            apply False.elim assump_41


variable (p3 p5 p0 p4 p7 p2 : Prop)
theorem file67_23060 : (((((p0 ∧ p2) ∨ (p3 → False)) → ((False → p5) ∨ (p7 → p7))) → False) → ((((True → p7) ∧ (p0 ∧ p4)) → False) ∧ (((p7 ∨ p3) → (p0 ∨ p2)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      have assump_62 : (((p0 ∧ p2) ∨ (p3 → False)) → ((False → p5) ∨ (p7 → p7))) := by
        intro assump_16
        cases assump_16
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply Or.inl
            intro assump_25
            apply False.elim assump_25
        case inr assump_18 =>
          apply Or.inl
          intro assump_30
          apply False.elim assump_30
      let assump_15 := assump_1 assump_62
      apply False.elim assump_15
  intro assump_36
  have assump_63 : (((p0 ∧ p2) ∨ (p3 → False)) → ((False → p5) ∨ (p7 → p7))) := by
    intro assump_42
    cases assump_42
    case inl assump_43 =>
      cases assump_43
      case intro assump_45 assump_46 =>
        apply Or.inl
        intro assump_51
        apply False.elim assump_51
    case inr assump_44 =>
      apply Or.inl
      intro assump_56
      apply False.elim assump_56
  let assump_41 := assump_1 assump_63
  apply False.elim assump_41


variable (p1 p3 : Prop)
theorem file67_24412 : (((((False ∧ p1) → False) ∧ ((p3 ∧ p1) ∨ (False → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p1) → False) ∧ ((p3 ∧ p1) ∨ (False → False))) := by
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
    apply Or.inr
    intro assump_10
    apply False.elim assump_10
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p6 p1 p3 p5 p4 p7 : Prop)
theorem file67_24916 : ((((((p6 ∨ True) ∨ (p3 → p1)) ∧ ((p4 → False) → (False ∧ True))) ∧ (((False ∨ p3) → False) → ((p0 ∧ p0) → False))) ∧ ((((p0 → p4) → (True ∨ p0)) → False) ∧ (((p0 → True) → False) ∨ ((p5 ∨ p7) ∨ (p1 → p4))))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_19
              case inl assump_22 =>
                have assump_171 : (p0 → True) := by
                  intro assump_27
                  apply True.intro
                let assump_26 := assump_22 assump_171
                apply False.elim assump_26
              case inr assump_23 =>
                cases assump_23
                case inl assump_31 =>
                  cases assump_31
                  case inl assump_33 =>
                    have assump_172 : ((p0 → p4) → (True ∨ p0)) := by
                      intro assump_39
                      apply Or.inl
                      apply True.intro
                    let assump_38 := assump_18 assump_172
                    apply False.elim assump_38
                  case inr assump_34 =>
                    have assump_173 : ((p0 → p4) → (True ∨ p0)) := by
                      intro assump_49
                      apply Or.inl
                      apply True.intro
                    let assump_48 := assump_18 assump_173
                    apply False.elim assump_48
                case inr assump_32 =>
                  have assump_174 : ((p0 → p4) → (True ∨ p0)) := by
                    intro assump_59
                    apply Or.inl
                    apply True.intro
                  let assump_58 := assump_18 assump_174
                  apply False.elim assump_58
          case inr assump_11 =>
            cases assump_3
            case intro assump_71 assump_72 =>
              cases assump_72
              case inl assump_75 =>
                have assump_175 : (p0 → True) := by
                  intro assump_80
                  apply True.intro
                let assump_79 := assump_75 assump_175
                apply False.elim assump_79
              case inr assump_76 =>
                cases assump_76
                case inl assump_84 =>
                  cases assump_84
                  case inl assump_86 =>
                    have assump_176 : ((p0 → p4) → (True ∨ p0)) := by
                      intro assump_92
                      apply Or.inl
                      apply True.intro
                    let assump_91 := assump_71 assump_176
                    apply False.elim assump_91
                  case inr assump_87 =>
                    have assump_177 : ((p0 → p4) → (True ∨ p0)) := by
                      intro assump_102
                      apply Or.inl
                      apply True.intro
                    let assump_101 := assump_71 assump_177
                    apply False.elim assump_101
                case inr assump_85 =>
                  have assump_178 : ((p0 → p4) → (True ∨ p0)) := by
                    intro assump_112
                    apply Or.inl
                    apply True.intro
                  let assump_111 := assump_71 assump_178
                  apply False.elim assump_111
        case inr assump_9 =>
          cases assump_3
          case intro assump_124 assump_125 =>
            cases assump_125
            case inl assump_128 =>
              have assump_179 : (p0 → True) := by
                intro assump_133
                apply True.intro
              let assump_132 := assump_128 assump_179
              apply False.elim assump_132
            case inr assump_129 =>
              cases assump_129
              case inl assump_137 =>
                cases assump_137
                case inl assump_139 =>
                  have assump_180 : ((p0 → p4) → (True ∨ p0)) := by
                    intro assump_145
                    apply Or.inl
                    apply True.intro
                  let assump_144 := assump_124 assump_180
                  apply False.elim assump_144
                case inr assump_140 =>
                  have assump_181 : ((p0 → p4) → (True ∨ p0)) := by
                    intro assump_155
                    apply Or.inl
                    apply True.intro
                  let assump_154 := assump_124 assump_181
                  apply False.elim assump_154
              case inr assump_138 =>
                have assump_182 : ((p0 → p4) → (True ∨ p0)) := by
                  intro assump_165
                  apply Or.inl
                  apply True.intro
                let assump_164 := assump_124 assump_182
                apply False.elim assump_164


variable (p1 p6 p5 p3 p7 p2 p0 : Prop)
theorem file67_29911 : (((((p1 ∧ p0) → False) → False) ∧ (((p7 → p2) → (True → True)) → False)) → ((((False ∨ p6) ∨ (p5 ∨ p3)) ∨ ((p5 → False) ∧ (p5 ∧ True))) ∨ (((p2 ∧ p7) ∧ (p1 ∨ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inr
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        cases assump_20
        case inl assump_27 =>
          have assump_51 : ((p7 → p2) → (True → True)) := by
            intro assump_35
            intro assump_36
            apply True.intro
          let assump_34 := assump_3 assump_51
          apply False.elim assump_34
        case inr assump_28 =>
          have assump_52 : ((p7 → p2) → (True → True)) := by
            intro assump_46
            intro assump_47
            apply True.intro
          let assump_45 := assump_3 assump_52
          apply False.elim assump_45


variable (p4 p6 p5 p1 p2 p7 p0 : Prop)
theorem file67_30921 : ((((((p6 ∧ p7) → False) → ((p5 ∨ p6) ∨ (p2 ∧ p5))) → False) ∧ ((((p1 → False) → (p1 ∧ True)) → False) ∧ (((p2 ∨ p1) ∧ (p0 ∧ p4)) ∧ ((p5 ∨ p2) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case inl assump_14 =>
            cases assump_13
            case intro assump_18 assump_19 =>
              have assump_51 : (p5 ∨ p2) := by
                apply Or.inr
                exact assump_14
              let assump_26 := assump_11 assump_51
              apply False.elim assump_26
          case inr assump_15 =>
            cases assump_13
            case intro assump_32 assump_33 =>
              have assump_52 : ((p1 → False) → (p1 ∧ True)) := by
                intro assump_45
                apply And.intro
                exact assump_15
                apply True.intro
              let assump_44 := assump_6 assump_52
              apply False.elim assump_44


variable (p5 p2 p7 : Prop)
theorem file67_32115 : (((((True → False) → False) ∨ ((p2 ∨ p7) ∧ (p2 → p5))) → False) → False) := by
  intro assump_1
  have assump_15 : (((True → False) → False) ∨ ((p2 ∨ p7) ∧ (p2 → p5))) := by
    apply Or.inl
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p3 p5 p2 p0 p1 : Prop)
theorem file67_32574 : ((((((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) → False) ∧ ((((p7 ∨ False) ∨ (p1 → p5)) ∨ ((False → False) ∨ (True → False))) ∧ (((p5 → p1) ∧ (p0 ∧ p3)) ∧ ((p0 ∨ p1) ∧ (p7 ∨ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_7
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_19
                case intro assump_22 assump_23 =>
                  cases assump_17
                  case intro assump_28 assump_29 =>
                    cases assump_28
                    case inl assump_30 =>
                      cases assump_29
                      case inl assump_34 =>
                        have assump_341 : (((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) := by
                          intro assump_45
                          cases assump_45
                          case intro assump_46 assump_47 =>
                            cases assump_46
                            case intro assump_48 assump_49 =>
                              cases assump_47
                              case inl assump_54 =>
                                apply Or.inl
                                intro assump_58
                                exact assump_23
                              case inr assump_55 =>
                                apply False.elim assump_55
                        let assump_44 := assump_2 assump_341
                        apply False.elim assump_44
                      case inr assump_35 =>
                        apply False.elim assump_35
                    case inr assump_31 =>
                      cases assump_29
                      case inl assump_70 =>
                        have assump_342 : (((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) := by
                          intro assump_81
                          cases assump_81
                          case intro assump_82 assump_83 =>
                            cases assump_82
                            case intro assump_84 assump_85 =>
                              cases assump_83
                              case inl assump_90 =>
                                apply Or.inl
                                intro assump_94
                                exact assump_23
                              case inr assump_91 =>
                                apply False.elim assump_91
                        let assump_80 := assump_2 assump_342
                        apply False.elim assump_80
                      case inr assump_71 =>
                        apply False.elim assump_71
          case inr assump_13 =>
            apply False.elim assump_13
        case inr assump_11 =>
          cases assump_7
          case intro assump_108 assump_109 =>
            cases assump_108
            case intro assump_110 assump_111 =>
              cases assump_111
              case intro assump_114 assump_115 =>
                cases assump_109
                case intro assump_120 assump_121 =>
                  cases assump_120
                  case inl assump_122 =>
                    cases assump_121
                    case inl assump_126 =>
                      have assump_343 : (((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) := by
                        intro assump_137
                        cases assump_137
                        case intro assump_138 assump_139 =>
                          cases assump_138
                          case intro assump_140 assump_141 =>
                            cases assump_139
                            case inl assump_146 =>
                              apply Or.inl
                              intro assump_150
                              exact assump_115
                            case inr assump_147 =>
                              apply False.elim assump_147
                      let assump_136 := assump_2 assump_343
                      apply False.elim assump_136
                    case inr assump_127 =>
                      apply False.elim assump_127
                  case inr assump_123 =>
                    cases assump_121
                    case inl assump_162 =>
                      have assump_344 : (((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) := by
                        intro assump_174
                        cases assump_174
                        case intro assump_175 assump_176 =>
                          cases assump_175
                          case intro assump_177 assump_178 =>
                            cases assump_176
                            case inl assump_183 =>
                              apply Or.inl
                              intro assump_187
                              exact assump_115
                            case inr assump_184 =>
                              apply False.elim assump_184
                      let assump_173 := assump_2 assump_344
                      apply False.elim assump_173
                    case inr assump_163 =>
                      apply False.elim assump_163
      case inr assump_9 =>
        cases assump_9
        case inl assump_197 =>
          cases assump_7
          case intro assump_201 assump_202 =>
            cases assump_201
            case intro assump_203 assump_204 =>
              cases assump_204
              case intro assump_207 assump_208 =>
                cases assump_202
                case intro assump_213 assump_214 =>
                  cases assump_213
                  case inl assump_215 =>
                    cases assump_214
                    case inl assump_219 =>
                      have assump_345 : (((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) := by
                        intro assump_230
                        cases assump_230
                        case intro assump_231 assump_232 =>
                          cases assump_231
                          case intro assump_233 assump_234 =>
                            cases assump_232
                            case inl assump_239 =>
                              apply Or.inl
                              intro assump_243
                              exact assump_208
                            case inr assump_240 =>
                              apply False.elim assump_240
                      let assump_229 := assump_2 assump_345
                      apply False.elim assump_229
                    case inr assump_220 =>
                      apply False.elim assump_220
                  case inr assump_216 =>
                    cases assump_214
                    case inl assump_255 =>
                      have assump_346 : (((p2 ∧ p2) ∧ (p2 ∨ False)) → ((p2 → p3) ∨ (False → True))) := by
                        intro assump_266
                        cases assump_266
                        case intro assump_267 assump_268 =>
                          cases assump_267
                          case intro assump_269 assump_270 =>
                            cases assump_268
                            case inl assump_275 =>
                              apply Or.inl
                              intro assump_279
                              exact assump_208
                            case inr assump_276 =>
                              apply False.elim assump_276
                      let assump_265 := assump_2 assump_346
                      apply False.elim assump_265
                    case inr assump_256 =>
                      apply False.elim assump_256
        case inr assump_198 =>
          cases assump_7
          case intro assump_291 assump_292 =>
            cases assump_291
            case intro assump_293 assump_294 =>
              cases assump_294
              case intro assump_297 assump_298 =>
                cases assump_292
                case intro assump_303 assump_304 =>
                  cases assump_303
                  case inl assump_305 =>
                    cases assump_304
                    case inl assump_309 =>
                      have assump_347 : True := by
                        apply True.intro
                      let assump_318 := assump_198 assump_347
                      apply False.elim assump_318
                    case inr assump_310 =>
                      apply False.elim assump_310
                  case inr assump_306 =>
                    cases assump_304
                    case inl assump_326 =>
                      have assump_348 : True := by
                        apply True.intro
                      let assump_335 := assump_198 assump_348
                      apply False.elim assump_335
                    case inr assump_327 =>
                      apply False.elim assump_327


variable (p2 p5 p4 p6 p7 p0 p1 p3 : Prop)
theorem file67_41742 : (((((p1 → p6) ∧ (p4 → p6)) → ((p7 ∧ True) ∨ (p3 ∨ p3))) ∧ (((False ∧ p6) → (p0 → False)) → ((True → False) → False))) → ((((p6 → p6) ∨ (p2 → p5)) ∨ ((p7 → False) ∧ (True → False))) ∨ (((p7 → False) ∨ (p5 ∧ p1)) ∧ ((True → False) ∨ (p5 → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8


variable (p4 p3 p0 p2 p6 p7 p1 : Prop)
theorem file67_42216 : (((((p0 → p6) → (True ∨ False)) → False) → (((True ∧ p7) ∧ (p7 ∨ False)) ∧ ((p3 ∧ p7) → (True ∧ p7)))) ∨ ((((p6 → p2) ∧ (p0 ∨ p1)) ∧ ((p3 → False) ∨ (p4 → p0))) → False)) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  apply And.intro
  apply True.intro
  have assump_29 : ((p0 → p6) → (True ∨ False)) := by
    intro assump_5
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4
  have assump_30 : ((p0 → p6) → (True ∨ False)) := by
    intro assump_14
    apply Or.inl
    apply True.intro
  let assump_13 := assump_1 assump_30
  apply False.elim assump_13
  intro assump_20
  apply And.intro
  apply True.intro
  cases assump_20
  case intro assump_21 assump_22 =>
    exact assump_22


variable (p3 p7 p6 p0 : Prop)
theorem file67_43036 : (((((p0 → False) → False) → ((p6 ∨ False) ∨ (p7 → False))) ∧ (((p3 ∨ True) → (True → False)) ∨ ((False → p0) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      have assump_24 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_10 := assump_6 assump_24
      have assump_25 : True := by
        apply True.intro
      let assump_11 := assump_10 assump_25
      apply False.elim assump_11
    case inr assump_7 =>
      have assump_26 : (False → p0) := by
        intro assump_18
        apply False.elim assump_18
      let assump_17 := assump_7 assump_26
      apply False.elim assump_17


variable (p0 p7 p2 : Prop)
theorem file67_43799 : (((((p0 ∨ True) → False) → False) ∧ (((p7 ∨ p7) ∧ (p0 → p2)) ∧ ((False → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          have assump_38 : (False → False) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_7 assump_38
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_39 : (False → False) := by
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_7 assump_39
          apply False.elim assump_31


variable (p4 p2 p1 p7 p3 : Prop)
theorem file67_44625 : (((((True → p7) ∧ (p3 → False)) ∨ ((p1 ∧ p4) ∨ (False → False))) ∧ (((True ∧ p3) → (p2 ∨ True)) ∧ ((p4 ∨ p4) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              have assump_94 : True := by
                apply True.intro
              let assump_24 := assump_17 assump_94
              apply False.elim assump_24
            case inr assump_19 =>
              have assump_95 : True := by
                apply True.intro
              let assump_32 := assump_17 assump_95
              apply False.elim assump_32
    case inr assump_5 =>
      cases assump_5
      case inl assump_36 =>
        cases assump_36
        case intro assump_38 assump_39 =>
          cases assump_3
          case intro assump_44 assump_45 =>
            cases assump_45
            case intro assump_48 assump_49 =>
              cases assump_48
              case inl assump_50 =>
                have assump_96 : True := by
                  apply True.intro
                let assump_56 := assump_49 assump_96
                apply False.elim assump_56
              case inr assump_51 =>
                have assump_97 : True := by
                  apply True.intro
                let assump_64 := assump_49 assump_97
                apply False.elim assump_64
      case inr assump_37 =>
        cases assump_3
        case intro assump_70 assump_71 =>
          cases assump_71
          case intro assump_74 assump_75 =>
            cases assump_74
            case inl assump_76 =>
              have assump_98 : True := by
                apply True.intro
              let assump_82 := assump_75 assump_98
              apply False.elim assump_82
            case inr assump_77 =>
              have assump_99 : True := by
                apply True.intro
              let assump_90 := assump_75 assump_99
              apply False.elim assump_90


variable (p2 p6 p1 p3 p5 : Prop)
theorem file67_46890 : ((((((p3 ∧ p5) ∨ (p6 ∧ False)) → ((False → p1) → False)) → (((p2 → p2) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p3 ∧ p5) ∨ (p6 ∧ False)) → ((False → p1) → False)) → (((p2 → p2) → False) → False)) := by
    intro assump_5
    intro assump_6
    have assump_23 : (p2 → p2) := by
      intro assump_13
      exact assump_13
    let assump_12 := assump_6 assump_23
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p2 p7 p0 p6 : Prop)
theorem file67_47446 : ((((((p6 ∨ False) ∧ (True → False)) ∧ ((p2 → False) ∨ (p0 ∧ p7))) → (((p2 → False) ∨ (p0 ∨ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_119 : ((((p6 ∨ False) ∧ (True → False)) ∧ ((p2 → False) ∨ (p0 ∧ p7))) → (((p2 → False) ∨ (p0 ∨ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_12
            case inl assump_21 =>
              have assump_120 : True := by
                apply True.intro
              let assump_26 := assump_14 assump_120
              apply False.elim assump_26
            case inr assump_22 =>
              cases assump_22
              case intro assump_30 assump_31 =>
                have assump_121 : True := by
                  apply True.intro
                let assump_38 := assump_14 assump_121
                apply False.elim assump_38
          case inr assump_16 =>
            apply False.elim assump_16
    case inr assump_8 =>
      cases assump_8
      case inl assump_44 =>
        cases assump_5
        case intro assump_48 assump_49 =>
          cases assump_48
          case intro assump_50 assump_51 =>
            cases assump_50
            case inl assump_52 =>
              cases assump_49
              case inl assump_58 =>
                have assump_122 : True := by
                  apply True.intro
                let assump_63 := assump_51 assump_122
                apply False.elim assump_63
              case inr assump_59 =>
                cases assump_59
                case intro assump_67 assump_68 =>
                  have assump_123 : True := by
                    apply True.intro
                  let assump_75 := assump_51 assump_123
                  apply False.elim assump_75
            case inr assump_53 =>
              apply False.elim assump_53
      case inr assump_45 =>
        cases assump_5
        case intro assump_83 assump_84 =>
          cases assump_83
          case intro assump_85 assump_86 =>
            cases assump_85
            case inl assump_87 =>
              cases assump_84
              case inl assump_93 =>
                have assump_124 : True := by
                  apply True.intro
                let assump_98 := assump_86 assump_124
                apply False.elim assump_98
              case inr assump_94 =>
                cases assump_94
                case intro assump_102 assump_103 =>
                  have assump_125 : True := by
                    apply True.intro
                  let assump_110 := assump_86 assump_125
                  apply False.elim assump_110
            case inr assump_88 =>
              apply False.elim assump_88
  let assump_4 := assump_1 assump_119
  apply False.elim assump_4


variable (p3 p7 p2 p1 p6 p5 p0 : Prop)
theorem file67_50452 : (((((p2 ∨ True) → False) → False) → False) → ((((p3 → False) → False) → ((p3 ∧ p3) → (p6 ∨ p3))) ∨ (((p2 ∧ p5) ∧ (p7 ∨ p0)) ∨ ((False → False) → (p1 ∧ False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inr
    exact assump_7


variable (p1 p3 p2 p0 p6 p4 p5 : Prop)
theorem file67_50836 : ((((((p0 ∨ p1) ∧ (p5 → False)) → False) ∧ (((p1 ∧ p1) → False) ∨ ((p5 ∨ p0) → (p2 ∨ p0)))) ∧ ((((p6 ∨ p3) → (p1 → p1)) → False) ∨ (((p4 → p2) ∧ (False ∧ p3)) ∧ ((p2 → False) ∨ (p1 ∧ True))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_3
        case inl assump_12 =>
          have assump_70 : ((p6 ∨ p3) → (p1 → p1)) := by
            intro assump_17
            intro assump_18
            cases assump_17
            case inl assump_21 =>
              exact assump_18
            case inr assump_22 =>
              exact assump_18
          let assump_16 := assump_12 assump_70
          apply False.elim assump_16
        case inr assump_13 =>
          cases assump_13
          case intro assump_30 assump_31 =>
            cases assump_30
            case intro assump_32 assump_33 =>
              cases assump_33
              case intro assump_36 assump_37 =>
                apply False.elim assump_36
      case inr assump_9 =>
        cases assump_3
        case inl assump_42 =>
          have assump_71 : ((p6 ∨ p3) → (p1 → p1)) := by
            intro assump_47
            intro assump_48
            cases assump_47
            case inl assump_51 =>
              exact assump_48
            case inr assump_52 =>
              exact assump_48
          let assump_46 := assump_42 assump_71
          apply False.elim assump_46
        case inr assump_43 =>
          cases assump_43
          case intro assump_60 assump_61 =>
            cases assump_60
            case intro assump_62 assump_63 =>
              cases assump_63
              case intro assump_66 assump_67 =>
                apply False.elim assump_66


variable (p1 p0 p7 p2 p6 : Prop)
theorem file67_52700 : ((((((p6 ∨ p2) → False) → ((p2 ∨ p6) ∨ (p2 ∨ True))) ∨ (((p1 → False) → False) → ((False → False) ∧ (p6 ∨ False)))) → ((((p0 ∧ p6) → False) ∧ ((False → True) → False)) ∧ (((False → True) ∨ (p6 ∨ p7)) → False))) → False) := by
  intro assump_1
  have assump_16 : ((((p6 ∨ p2) → False) → ((p2 ∨ p6) ∨ (p2 ∨ True))) ∨ (((p1 → False) → False) → ((False → False) ∧ (p6 ∨ False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_16
  let assump_8 := And.left assump_4
  let assump_9 := And.right assump_8
  have assump_17 : (False → True) := by
    intro assump_12
    apply True.intro
  let assump_11 := assump_9 assump_17
  apply False.elim assump_11


variable (p6 p0 p3 p5 p1 p2 p4 p7 : Prop)
theorem file67_53497 : (((((p1 → p2) ∧ (p7 ∧ True)) → ((p7 ∨ p3) ∨ (p3 → False))) ∨ (((False → False) → (p2 → p0)) → False)) ∨ ((((p1 → True) ∨ (p6 → False)) → ((True → p4) ∨ (p3 ∧ p6))) ∧ (((p7 ∨ p1) → False) ∨ ((p5 ∨ p0) ∧ (p1 ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      apply Or.inl
      exact assump_6


variable (p6 p7 p1 p4 p3 p5 : Prop)
theorem file67_53991 : (((((p3 → p1) → False) ∧ ((p7 → p7) → False)) ∧ (((p6 → p7) ∨ (p3 ∧ p6)) ∨ ((False ∧ p5) → (p4 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          have assump_49 : (p7 → p7) := by
            intro assump_18
            exact assump_18
          let assump_17 := assump_5 assump_49
          apply False.elim assump_17
        case inr assump_13 =>
          cases assump_13
          case intro assump_24 assump_25 =>
            have assump_50 : (p7 → p7) := by
              intro assump_33
              exact assump_33
            let assump_32 := assump_5 assump_50
            apply False.elim assump_32
      case inr assump_11 =>
        have assump_51 : (p7 → p7) := by
          intro assump_43
          exact assump_43
        let assump_42 := assump_5 assump_51
        apply False.elim assump_42


variable (p7 p5 p0 p3 p6 p2 p1 : Prop)
theorem file67_55076 : ((((((p3 → False) → False) → False) ∧ (((True ∨ p0) ∨ (p6 → p2)) ∧ ((p1 → True) → False))) ∨ ((((p6 ∨ p2) ∧ (p5 → p1)) → ((p6 ∧ p0) → (True → False))) ∧ (((p7 → p5) → (p6 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            have assump_53 : (p1 → True) := by
              intro assump_19
              apply True.intro
            let assump_18 := assump_9 assump_53
            apply False.elim assump_18
          case inr assump_13 =>
            have assump_54 : (p1 → True) := by
              intro assump_28
              apply True.intro
            let assump_27 := assump_9 assump_54
            apply False.elim assump_27
        case inr assump_11 =>
          have assump_55 : (p1 → True) := by
            intro assump_37
            apply True.intro
          let assump_36 := assump_9 assump_55
          apply False.elim assump_36
  case inr assump_3 =>
    cases assump_3
    case intro assump_41 assump_42 =>
      have assump_56 : ((p7 → p5) → (p6 → True)) := by
        intro assump_48
        intro assump_49
        apply True.intro
      let assump_47 := assump_42 assump_56
      apply False.elim assump_47


variable (p2 p6 p5 p4 p1 p3 p7 : Prop)
theorem file67_56548 : (((((p6 ∨ p2) → False) ∨ ((p5 ∨ p3) → (p7 ∨ False))) ∧ (((p4 ∧ p3) → (p6 → p6)) → False)) → ((((p1 → False) ∨ (p7 ∨ p1)) ∧ ((p6 ∧ p2) ∧ (p2 ∨ p5))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_10
          case inl assump_17 =>
            cases assump_1
            case intro assump_21 assump_22 =>
              cases assump_21
              case inl assump_23 =>
                have assump_297 : ((p4 ∧ p3) → (p6 → p6)) := by
                  intro assump_30
                  intro assump_31
                  cases assump_30
                  case intro assump_34 assump_35 =>
                    exact assump_31
                let assump_29 := assump_22 assump_297
                apply False.elim assump_29
              case inr assump_24 =>
                have assump_298 : ((p4 ∧ p3) → (p6 → p6)) := by
                  intro assump_48
                  intro assump_49
                  cases assump_48
                  case intro assump_52 assump_53 =>
                    exact assump_49
                let assump_47 := assump_22 assump_298
                apply False.elim assump_47
          case inr assump_18 =>
            cases assump_1
            case intro assump_63 assump_64 =>
              cases assump_63
              case inl assump_65 =>
                have assump_299 : ((p4 ∧ p3) → (p6 → p6)) := by
                  intro assump_72
                  intro assump_73
                  cases assump_72
                  case intro assump_76 assump_77 =>
                    exact assump_73
                let assump_71 := assump_64 assump_299
                apply False.elim assump_71
              case inr assump_66 =>
                have assump_300 : ((p4 ∧ p3) → (p6 → p6)) := by
                  intro assump_90
                  intro assump_91
                  cases assump_90
                  case intro assump_94 assump_95 =>
                    exact assump_91
                let assump_89 := assump_64 assump_300
                apply False.elim assump_89
    case inr assump_6 =>
      cases assump_6
      case inl assump_103 =>
        cases assump_4
        case intro assump_107 assump_108 =>
          cases assump_107
          case intro assump_109 assump_110 =>
            cases assump_108
            case inl assump_115 =>
              cases assump_1
              case intro assump_119 assump_120 =>
                cases assump_119
                case inl assump_121 =>
                  have assump_301 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_128
                    intro assump_129
                    cases assump_128
                    case intro assump_132 assump_133 =>
                      exact assump_129
                  let assump_127 := assump_120 assump_301
                  apply False.elim assump_127
                case inr assump_122 =>
                  have assump_302 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_146
                    intro assump_147
                    cases assump_146
                    case intro assump_150 assump_151 =>
                      exact assump_147
                  let assump_145 := assump_120 assump_302
                  apply False.elim assump_145
            case inr assump_116 =>
              cases assump_1
              case intro assump_161 assump_162 =>
                cases assump_161
                case inl assump_163 =>
                  have assump_303 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_170
                    intro assump_171
                    cases assump_170
                    case intro assump_174 assump_175 =>
                      exact assump_171
                  let assump_169 := assump_162 assump_303
                  apply False.elim assump_169
                case inr assump_164 =>
                  have assump_304 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_188
                    intro assump_189
                    cases assump_188
                    case intro assump_192 assump_193 =>
                      exact assump_189
                  let assump_187 := assump_162 assump_304
                  apply False.elim assump_187
      case inr assump_104 =>
        cases assump_4
        case intro assump_203 assump_204 =>
          cases assump_203
          case intro assump_205 assump_206 =>
            cases assump_204
            case inl assump_211 =>
              cases assump_1
              case intro assump_215 assump_216 =>
                cases assump_215
                case inl assump_217 =>
                  have assump_305 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_224
                    intro assump_225
                    cases assump_224
                    case intro assump_228 assump_229 =>
                      exact assump_225
                  let assump_223 := assump_216 assump_305
                  apply False.elim assump_223
                case inr assump_218 =>
                  have assump_306 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_242
                    intro assump_243
                    cases assump_242
                    case intro assump_246 assump_247 =>
                      exact assump_243
                  let assump_241 := assump_216 assump_306
                  apply False.elim assump_241
            case inr assump_212 =>
              cases assump_1
              case intro assump_257 assump_258 =>
                cases assump_257
                case inl assump_259 =>
                  have assump_307 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_266
                    intro assump_267
                    cases assump_266
                    case intro assump_270 assump_271 =>
                      exact assump_267
                  let assump_265 := assump_258 assump_307
                  apply False.elim assump_265
                case inr assump_260 =>
                  have assump_308 : ((p4 ∧ p3) → (p6 → p6)) := by
                    intro assump_284
                    intro assump_285
                    cases assump_284
                    case intro assump_288 assump_289 =>
                      exact assump_285
                  let assump_283 := assump_258 assump_308
                  apply False.elim assump_283


variable (p2 p6 p4 p7 : Prop)
theorem file67_63214 : (((((False ∨ False) → (True ∨ p6)) ∨ ((p4 ∧ p7) ∧ (p2 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((False ∨ False) → (True ∨ p6)) ∨ ((p4 ∧ p7) ∧ (p2 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply False.elim assump_6
    case inr assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p5 p0 p7 p2 p3 : Prop)
theorem file67_63699 : (((((True → False) → (p5 ∧ p3)) ∧ ((p2 → False) ∧ (True → False))) → False) ∧ ((((True ∧ p3) → (True ∨ p0)) → False) → (((p7 ∧ False) → False) ∨ ((False ∨ p7) → False)))) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_26 : True := by
        apply True.intro
      let assump_12 := assump_7 assump_26
      apply False.elim assump_12
  intro assump_16
  apply Or.inl
  intro assump_19
  cases assump_19
  case intro assump_20 assump_21 =>
    apply False.elim assump_21


variable (p7 p2 p0 p1 : Prop)
theorem file67_64341 : (((((False ∨ p2) ∧ (False ∧ p0)) → ((True ∨ p1) → (p7 ∧ p2))) → False) → False) := by
  intro assump_1
  have assump_70 : (((False ∨ p2) ∧ (False ∧ p0)) → ((True ∨ p1) → (p7 ∧ p2))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          cases assump_12
          case intro assump_19 assump_20 =>
            apply False.elim assump_19
    case inr assump_8 =>
      cases assump_5
      case intro assump_25 assump_26 =>
        cases assump_25
        case inl assump_27 =>
          apply False.elim assump_27
        case inr assump_28 =>
          cases assump_26
          case intro assump_33 assump_34 =>
            apply False.elim assump_33
    cases assump_6
    case inl assump_37 =>
      cases assump_5
      case intro assump_41 assump_42 =>
        cases assump_41
        case inl assump_43 =>
          apply False.elim assump_43
        case inr assump_44 =>
          cases assump_42
          case intro assump_49 assump_50 =>
            apply False.elim assump_49
    case inr assump_38 =>
      cases assump_5
      case intro assump_55 assump_56 =>
        cases assump_55
        case inl assump_57 =>
          apply False.elim assump_57
        case inr assump_58 =>
          cases assump_56
          case intro assump_63 assump_64 =>
            apply False.elim assump_63
  let assump_4 := assump_1 assump_70
  apply False.elim assump_4


variable (p3 p5 p7 p4 p6 p1 p2 p0 : Prop)
theorem file67_66022 : ((((((p5 ∨ True) ∨ (True ∧ p4)) → ((p1 ∨ p6) ∧ (p4 ∨ p3))) ∨ (((p6 ∧ p7) → False) → ((p5 → p1) ∨ (True → False)))) ∧ ((((p5 → False) → (False → p2)) ∨ ((p7 ∧ p0) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_30 : (((p5 → False) → (False → p2)) ∨ ((p7 ∧ p0) → False)) := by
        apply Or.inl
        intro assump_11
        intro assump_12
        apply False.elim assump_12
      let assump_10 := assump_3 assump_30
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_31 : (((p5 → False) → (False → p2)) ∨ ((p7 ∧ p0) → False)) := by
        apply Or.inl
        intro assump_23
        intro assump_24
        apply False.elim assump_24
      let assump_22 := assump_3 assump_31
      apply False.elim assump_22


variable (p2 p6 p5 p7 p1 : Prop)
theorem file67_66937 : ((((((p6 ∧ p1) → False) → ((False ∧ False) → (True ∧ p2))) ∧ (((False → p7) → False) → ((False → False) → (p5 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_27 : ((((p6 ∧ p1) → False) → ((False ∧ False) → (True ∧ p2))) ∧ (((False → p7) → False) → ((False → False) → (p5 ∨ p5)))) := by
    apply And.intro
    intro assump_5
    intro assump_6
    apply And.intro
    apply True.intro
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_7
    intro assump_11
    intro assump_12
    have assump_28 : (False → p7) := by
      intro assump_18
      apply False.elim assump_18
    let assump_17 := assump_11 assump_28
    apply False.elim assump_17
  let assump_4 := assump_1 assump_27
  apply False.elim assump_4


variable (p0 p1 p7 p5 p6 p2 p4 p3 : Prop)
theorem file67_67763 : (((((False ∧ p2) → False) ∨ ((True → p1) ∧ (p2 → p2))) ∧ (((p5 ∧ p6) ∨ (p4 → p4)) ∨ ((p1 ∧ p0) → False))) ∨ ((((p1 → p1) → False) ∧ ((p7 → False) ∨ (p2 ∧ p3))) ∨ (((p6 → False) → (False ∨ p2)) ∧ ((p6 ∨ p3) → (p4 → p1))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    apply False.elim assump_19
  apply Or.inl
  apply Or.inr
  intro assump_23
  exact assump_23


variable (p3 p5 p6 p4 p2 : Prop)
theorem file67_68265 : (((((p3 ∨ p4) → (p2 ∨ p5)) ∧ ((p2 ∨ p6) → (True ∨ True))) → False) → ((((p3 → False) → False) → ((p5 ∧ False) → (p5 → False))) ∨ (((p5 ∧ True) ∧ (p2 ∨ p2)) ∨ ((False ∧ p4) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_5
  case intro assump_9 assump_10 =>
    apply False.elim assump_10


variable (p3 p6 p1 p0 p2 p7 : Prop)
theorem file67_68681 : (((((p0 ∧ p0) → False) → ((p3 → False) ∨ (p6 → p0))) → (((p1 → p2) → (False → p6)) → False)) → ((((p3 ∨ p1) ∧ (p3 ∧ p7)) ∨ ((True → p2) ∧ (p3 ∧ False))) → (((p0 ∨ False) → False) ∨ ((p0 → False) ∧ (p3 → p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          apply Or.inl
          intro assump_19
          cases assump_19
          case inl assump_20 =>
            have assump_95 : (((p0 ∧ p0) → False) → ((p3 → False) ∨ (p6 → p0))) := by
              intro assump_26
              apply Or.inl
              intro assump_29
              have assump_96 : (p0 ∧ p0) := by
                apply And.intro
                exact assump_20
                exact assump_20
              let assump_33 := assump_26 assump_96
              apply False.elim assump_33
            let assump_25 := assump_1 assump_95
            have assump_97 : ((p1 → p2) → (False → p6)) := by
              intro assump_38
              intro assump_39
              apply False.elim assump_39
            let assump_37 := assump_25 assump_97
            apply False.elim assump_37
          case inr assump_21 =>
            apply False.elim assump_21
      case inr assump_8 =>
        cases assump_6
        case intro assump_49 assump_50 =>
          apply Or.inl
          intro assump_57
          cases assump_57
          case inl assump_58 =>
            have assump_98 : (((p0 ∧ p0) → False) → ((p3 → False) ∨ (p6 → p0))) := by
              intro assump_64
              apply Or.inl
              intro assump_67
              have assump_99 : (p0 ∧ p0) := by
                apply And.intro
                exact assump_58
                exact assump_58
              let assump_71 := assump_64 assump_99
              apply False.elim assump_71
            let assump_63 := assump_1 assump_98
            have assump_100 : ((p1 → p2) → (False → p6)) := by
              intro assump_76
              intro assump_77
              apply False.elim assump_77
            let assump_75 := assump_63 assump_100
            apply False.elim assump_75
          case inr assump_59 =>
            apply False.elim assump_59
  case inr assump_4 =>
    cases assump_4
    case intro assump_85 assump_86 =>
      cases assump_86
      case intro assump_89 assump_90 =>
        apply False.elim assump_90


variable (p6 p4 p7 p0 p1 : Prop)
theorem file67_71238 : ((((((p4 → False) ∨ (False ∧ p6)) ∧ ((p0 ∨ p4) ∧ (p6 → False))) → (((p7 ∨ p4) ∧ (p1 ∧ p1)) → False)) ∧ ((((p0 ∧ p0) → False) → ((p7 ∧ True) → False)) ∧ (((p4 → True) ∨ (p1 ∧ p7)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_17 : ((p4 → True) ∨ (p1 ∧ p7)) := by
        apply Or.inl
        intro assump_13
        apply True.intro
      let assump_12 := assump_7 assump_17
      apply False.elim assump_12


variable (p1 p7 p2 p6 p0 p5 : Prop)
theorem file67_71826 : (((((p2 ∨ False) → False) ∨ ((True → p1) → False)) ∨ (((p5 ∧ p1) → (p6 → False)) ∧ ((True ∨ p1) ∧ (p1 → False)))) → ((((p5 ∨ p7) ∨ (False ∨ True)) ∨ ((p0 → False) ∧ (p1 ∨ p0))) ∨ (((p5 ∧ p6) ∨ (p7 ∧ p0)) ∨ ((p5 → False) → (False ∧ p5))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply Or.inr
      apply True.intro
    case inr assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply Or.inr
      apply True.intro
  case inr assump_3 =>
    cases assump_3
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        cases assump_14
        case inl assump_16 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply Or.inr
          apply True.intro
        case inr assump_17 =>
          apply Or.inl
          apply Or.inl
          apply Or.inr
          apply Or.inr
          apply True.intro


variable (p3 p7 p2 p6 p5 p4 : Prop)
theorem file67_72919 : ((((((p4 ∨ p2) ∨ (p3 → p6)) ∧ ((p5 → p4) → False)) → (((True ∨ True) → (p2 → False)) → ((p4 → p3) ∨ (p3 → False)))) ∧ ((((p5 ∨ True) ∧ (p4 ∧ False)) → ((False → p7) ∧ (p3 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p5 ∨ True) ∧ (p4 ∧ False)) → ((False → p7) ∧ (p3 → True))) := by
      intro assump_9
      apply And.intro
      intro assump_10
      apply False.elim assump_10
      intro assump_13
      apply True.intro
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p7 p2 p0 p6 p1 p3 p4 : Prop)
theorem file67_73557 : (((((p0 → True) → False) → False) ∨ (((p7 → True) → False) → False)) ∨ ((((p2 ∨ p6) ∧ (p4 → False)) ∨ ((p2 ∨ p3) → False)) ∨ (((p4 → p1) → False) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_9 : (p0 → True) := by
    intro assump_5
    apply True.intro
  let assump_4 := assump_1 assump_9
  apply False.elim assump_4


variable (p1 p5 p7 p0 p4 p6 p2 p3 : Prop)
theorem file67_73973 : (((((p1 ∧ p2) ∧ (p4 → p5)) ∧ ((True ∧ p4) ∧ (True ∧ False))) → (((p0 ∧ False) → (p3 ∨ p2)) ∨ ((p6 ∧ False) → False))) ∨ ((((False ∧ p1) ∧ (False ∨ True)) → False) ∨ (((p4 ∨ p7) ∧ (p4 → p1)) → ((p3 ∨ p6) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_15
            case intro assump_22 assump_23 =>
              apply False.elim assump_23


variable (p5 p1 p4 p7 : Prop)
theorem file67_74702 : (((((p5 ∨ False) → False) ∨ ((p7 → False) ∧ (p5 → p4))) ∧ (((p1 → False) → (p1 → False)) → False)) → False) := by
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    cases assump_11
    case inl assump_13 =>
      have assump_55 : ((p1 → False) → (p1 → False)) := by
        intro assump_20
        intro assump_21
        have assump_56 : p1 := by
          exact assump_21
        let assump_26 := assump_20 assump_56
        apply False.elim assump_26
      let assump_19 := assump_12 assump_55
      apply False.elim assump_19
    case inr assump_14 =>
      cases assump_14
      case intro assump_33 assump_34 =>
        have assump_57 : ((p1 → False) → (p1 → False)) := by
          intro assump_42
          intro assump_43
          have assump_58 : p1 := by
            exact assump_43
          let assump_48 := assump_42 assump_58
          apply False.elim assump_48
        let assump_41 := assump_12 assump_57
        apply False.elim assump_41


variable (p0 p3 p7 p1 p2 p4 : Prop)
theorem file67_75746 : (((((p0 ∧ p4) ∨ (p4 ∧ p4)) ∧ ((True → False) ∧ (p4 → False))) → (((False ∧ False) → False) → False)) ∨ ((((p2 ∨ p1) ∧ (True → True)) ∨ ((p1 ∨ False) ∨ (p3 ∨ False))) ∨ (((p0 → p7) → (p7 ∨ p0)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_6
        case intro assump_15 assump_16 =>
          have assump_41 : p4 := by
            exact assump_10
          let assump_21 := assump_16 assump_41
          apply False.elim assump_21
    case inr assump_8 =>
      cases assump_8
      case intro assump_25 assump_26 =>
        cases assump_6
        case intro assump_31 assump_32 =>
          have assump_42 : p4 := by
            exact assump_26
          let assump_37 := assump_32 assump_42
          apply False.elim assump_37


variable (p6 p0 p1 p7 p3 p5 : Prop)
theorem file67_76732 : (((((p1 ∨ p5) ∧ (p0 ∧ p1)) → ((False ∨ False) → (p3 ∧ p6))) ∧ (((True → True) → (False ∧ p0)) → ((p3 ∧ True) ∨ (p6 ∧ p6)))) ∨ ((((p7 ∨ p1) → False) ∨ ((True → True) → (p3 → False))) → False)) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    apply False.elim assump_3
  case inr assump_4 =>
    apply False.elim assump_4
  cases assump_2
  case inl assump_9 =>
    apply False.elim assump_9
  case inr assump_10 =>
    apply False.elim assump_10
  intro assump_15
  have assump_24 : (True → True) := by
    intro assump_19
    apply True.intro
  let assump_18 := assump_15 assump_24
  let assump_20 := And.left assump_18
  apply False.elim assump_20


variable (p4 p5 p6 p7 p2 : Prop)
theorem file67_77524 : (((((p5 ∧ False) ∧ (p4 ∧ p7)) ∧ ((p5 → False) → False)) ∧ (((p5 → p6) → (p7 → False)) → False)) → ((((p2 → p2) → (p6 → True)) ∨ ((False → False) ∧ (p4 ∨ p2))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_11
          case intro assump_13 assump_14 =>
            apply False.elim assump_14
  case inr assump_4 =>
    cases assump_4
    case intro assump_19 assump_20 =>
      cases assump_20
      case inl assump_23 =>
        cases assump_1
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            cases assump_29
            case intro assump_31 assump_32 =>
              cases assump_31
              case intro assump_33 assump_34 =>
                apply False.elim assump_34
      case inr assump_24 =>
        cases assump_1
        case intro assump_41 assump_42 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            cases assump_43
            case intro assump_45 assump_46 =>
              cases assump_45
              case intro assump_47 assump_48 =>
                apply False.elim assump_48


variable (p1 p7 p0 p4 : Prop)
theorem file67_78934 : (((((p0 ∧ p1) ∨ (p7 ∨ p7)) → ((True → False) → (p4 → False))) → False) → False) := by
  intro assump_1
  have assump_45 : (((p0 ∧ p1) ∨ (p7 ∨ p7)) → ((True → False) → (p4 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_46 : True := by
          apply True.intro
        let assump_22 := assump_6 assump_46
        apply False.elim assump_22
    case inr assump_13 =>
      cases assump_13
      case inl assump_26 =>
        have assump_47 : True := by
          apply True.intro
        let assump_31 := assump_6 assump_47
        apply False.elim assump_31
      case inr assump_27 =>
        have assump_48 : True := by
          apply True.intro
        let assump_38 := assump_6 assump_48
        apply False.elim assump_38
  let assump_4 := assump_1 assump_45
  apply False.elim assump_4


variable (p7 p6 p5 p4 : Prop)
theorem file67_79935 : ((((((p5 ∧ p6) → (False ∨ p6)) → False) → (((p4 → False) → (p7 ∨ True)) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p5 ∧ p6) → (False ∨ p6)) → False) → (((p4 → False) → (p7 ∨ True)) → False)) := by
    intro assump_5
    intro assump_6
    have assump_26 : ((p5 ∧ p6) → (False ∨ p6)) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply Or.inr
        exact assump_14
    let assump_11 := assump_5 assump_26
    apply False.elim assump_11
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p1 p0 p6 p2 p3 p4 : Prop)
theorem file67_80580 : (((((p3 ∧ p1) ∨ (False → False)) ∨ ((p2 → False) ∨ (p2 ∨ p0))) → False) → ((((p6 → p4) ∨ (False → False)) ∧ ((True → False) → (False → p1))) ∧ (((p2 → p3) → False) ∧ ((p1 → False) → (p6 ∨ p2))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_43 : (((p3 ∧ p1) ∨ (False → False)) ∨ ((p2 → False) ∨ (p2 ∨ p0))) := by
    apply Or.inl
    apply Or.inr
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_43
  apply False.elim assump_8
  intro assump_15
  intro assump_16
  apply False.elim assump_16
  apply And.intro
  intro assump_19
  have assump_44 : (((p3 ∧ p1) ∨ (False → False)) ∨ ((p2 → False) ∨ (p2 ∨ p0))) := by
    apply Or.inl
    apply Or.inr
    intro assump_25
    apply False.elim assump_25
  let assump_24 := assump_1 assump_44
  apply False.elim assump_24
  intro assump_31
  have assump_45 : (((p3 ∧ p1) ∨ (False → False)) ∨ ((p2 → False) ∨ (p2 ∨ p0))) := by
    apply Or.inl
    apply Or.inr
    intro assump_37
    apply False.elim assump_37
  let assump_36 := assump_1 assump_45
  apply False.elim assump_36


variable (p7 p3 p5 p2 p6 p1 : Prop)
theorem file67_81756 : (((((False ∧ p7) → (p3 ∧ p5)) → False) → (((p1 ∧ False) ∨ (p3 → True)) → ((False → False) ∨ (p1 → False)))) ∨ ((((p5 ∨ p1) → False) ∧ ((p6 → p3) ∧ (True ∨ p2))) ∧ (((p5 → p6) → (p5 ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6
  case inr assump_4 =>
    apply Or.inl
    intro assump_15
    apply False.elim assump_15


variable (p4 p2 p6 p5 p1 p7 p0 p3 : Prop)
theorem file67_82294 : ((((((p7 → False) → (p4 → p1)) → False) ∧ (((False → False) → False) ∧ ((p2 ∧ p3) → (p4 → False)))) ∧ ((((p5 → True) → (p1 ∧ p7)) ∧ ((p7 ∨ p0) ∨ (p4 → p5))) ∧ (((p4 ∧ p6) ∧ (p5 → False)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_9
      case intro assump_12 assump_13 =>
        cases assump_7
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_21
            case inl assump_24 =>
              cases assump_24
              case inl assump_26 =>
                have assump_85 : (False → False) := by
                  intro assump_41
                  apply False.elim assump_41
                let assump_40 := assump_12 assump_85
                apply False.elim assump_40
              case inr assump_27 =>
                have assump_86 : (False → False) := by
                  intro assump_60
                  apply False.elim assump_60
                let assump_59 := assump_12 assump_86
                apply False.elim assump_59
            case inr assump_25 =>
              have assump_87 : (False → False) := by
                intro assump_79
                apply False.elim assump_79
              let assump_78 := assump_12 assump_87
              apply False.elim assump_78


variable (p5 p7 p6 p1 p2 p0 p3 : Prop)
theorem file67_83767 : (((((p2 ∨ p6) → (p2 ∧ p0)) → ((p5 → p3) → (False → False))) ∨ (((p7 ∧ p0) → (p6 → False)) → False)) ∨ ((((True → p0) → (p1 ∨ False)) → False) ∨ (((p3 → p2) → (p3 ∨ p2)) ∨ ((p5 → False) ∨ (True ∧ p3))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p0 p2 p1 p3 p7 p4 p6 : Prop)
theorem file67_84148 : (((((False ∨ p6) ∨ (p2 ∨ p7)) → False) → False) → ((((p1 ∨ p4) → (p3 ∧ p0)) ∧ ((False ∧ p3) ∧ (False → False))) → (((p4 → p0) → False) → ((False ∨ p1) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply False.elim assump_5
  case inr assump_6 =>
    cases assump_2
    case intro assump_13 assump_14 =>
      cases assump_14
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply False.elim assump_19


variable (p0 p3 p4 p2 p6 : Prop)
theorem file67_84757 : (((((p0 ∧ p3) ∨ (p0 → True)) → False) → (((True ∧ p6) → False) ∨ ((p0 → True) → False))) ∨ ((((False ∨ p3) ∧ (p0 → False)) ∨ ((p6 → False) → False)) ∨ (((p0 ∨ p0) → False) ∧ ((p4 ∨ p2) → (p6 ∧ p3))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_17 : ((p0 ∧ p3) ∨ (p0 → True)) := by
      apply Or.inr
      intro assump_13
      apply True.intro
    let assump_12 := assump_1 assump_17
    apply False.elim assump_12


variable (p3 p6 p0 p1 : Prop)
theorem file67_85321 : ((((((p0 → p6) → False) ∧ ((p0 → False) ∨ (p0 → False))) → (((p3 ∧ False) → False) ∧ ((False ∧ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p0 → p6) → False) ∧ ((p0 → False) ∨ (p0 → False))) → (((p3 ∧ False) → False) ∧ ((False ∧ p1) → False))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply False.elim assump_8
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p4 p5 p0 p3 p6 p7 p1 p2 : Prop)
theorem file67_85992 : ((((((p4 ∧ p0) ∧ (p3 ∨ p4)) ∧ ((True → p5) → False)) ∧ (((True ∨ False) → False) → ((p7 ∨ False) ∨ (False ∨ p6)))) ∧ ((((True ∨ p2) → False) → False) ∧ (((p6 ∨ p7) ∧ (True → False)) ∧ ((p0 → p1) ∧ (p3 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_9
            case inl assump_16 =>
              cases assump_3
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case inl assump_32 =>
                      cases assump_29
                      case intro assump_38 assump_39 =>
                        cases assump_39
                        case intro assump_42 assump_43 =>
                          have assump_138 : True := by
                            apply True.intro
                          let assump_52 := assump_31 assump_138
                          apply False.elim assump_52
                    case inr assump_33 =>
                      cases assump_29
                      case intro assump_60 assump_61 =>
                        cases assump_61
                        case intro assump_64 assump_65 =>
                          have assump_139 : True := by
                            apply True.intro
                          let assump_74 := assump_31 assump_139
                          apply False.elim assump_74
            case inr assump_17 =>
              cases assump_3
              case intro assump_84 assump_85 =>
                cases assump_85
                case intro assump_88 assump_89 =>
                  cases assump_88
                  case intro assump_90 assump_91 =>
                    cases assump_90
                    case inl assump_92 =>
                      cases assump_89
                      case intro assump_98 assump_99 =>
                        cases assump_99
                        case intro assump_102 assump_103 =>
                          have assump_140 : True := by
                            apply True.intro
                          let assump_112 := assump_91 assump_140
                          apply False.elim assump_112
                    case inr assump_93 =>
                      cases assump_89
                      case intro assump_120 assump_121 =>
                        cases assump_121
                        case intro assump_124 assump_125 =>
                          have assump_141 : True := by
                            apply True.intro
                          let assump_134 := assump_91 assump_141
                          apply False.elim assump_134


variable (p4 p7 p6 p5 p1 : Prop)
theorem file67_89061 : (((((p6 ∧ p4) ∧ (p4 ∨ p5)) ∧ ((p4 ∨ p6) → (p4 ∧ p1))) ∧ (((False → p6) → False) ∧ ((p5 → p4) ∧ (p7 ∧ False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_7
          case inl assump_14 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  apply False.elim assump_29
          case inr assump_15 =>
            cases assump_3
            case intro assump_38 assump_39 =>
              cases assump_39
              case intro assump_42 assump_43 =>
                cases assump_43
                case intro assump_46 assump_47 =>
                  apply False.elim assump_47


variable (p0 p6 p1 p3 p2 p4 : Prop)
theorem file67_90137 : (((((p3 ∨ True) → (p4 ∧ False)) → False) → False) → ((((p2 → p1) ∨ (p6 → p1)) ∧ ((p4 ∨ p0) ∨ (p6 ∧ p2))) ∧ (((p6 ∧ p3) ∨ (p0 → p2)) → ((p0 → False) ∨ (True → p4))))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  apply Or.inl
  intro assump_4
  have assump_85 : (((p3 ∨ True) → (p4 ∧ False)) → False) := by
    intro assump_9
    have assump_86 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_9 assump_86
    let assump_13 := And.right assump_12
    apply False.elim assump_13
  let assump_8 := assump_1 assump_85
  apply False.elim assump_8
  have assump_87 : (((p3 ∨ True) → (p4 ∧ False)) → False) := by
    intro assump_24
    have assump_88 : (p3 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_27 := assump_24 assump_88
    let assump_28 := And.right assump_27
    apply False.elim assump_28
  let assump_23 := assump_1 assump_87
  apply False.elim assump_23
  intro assump_36
  cases assump_36
  case inl assump_37 =>
    cases assump_37
    case intro assump_39 assump_40 =>
      apply Or.inl
      intro assump_47
      have assump_89 : (((p3 ∨ True) → (p4 ∧ False)) → False) := by
        intro assump_52
        have assump_90 : (p3 ∨ True) := by
          apply Or.inl
          exact assump_40
        let assump_55 := assump_52 assump_90
        let assump_56 := And.right assump_55
        apply False.elim assump_56
      let assump_51 := assump_1 assump_89
      apply False.elim assump_51
  case inr assump_38 =>
    apply Or.inl
    intro assump_68
    have assump_91 : (((p3 ∨ True) → (p4 ∧ False)) → False) := by
      intro assump_73
      have assump_92 : (p3 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_76 := assump_73 assump_92
      let assump_77 := And.right assump_76
      apply False.elim assump_77
    let assump_72 := assump_1 assump_91
    apply False.elim assump_72


variable (p2 p6 p1 p3 p4 p5 : Prop)
theorem file67_92109 : (((((p3 ∨ p4) → (p2 → p3)) ∧ ((True ∨ True) → False)) → False) ∧ ((((False → False) → False) → ((p1 → False) → (False ∧ False))) ∨ (((p6 → p2) ∨ (False ∨ p5)) ∧ ((p2 ∧ p1) ∨ (True ∧ p3))))) := by
  apply And.intro
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    have assump_45 : (True ∨ True) := by
      apply Or.inl
      apply True.intro
    let assump_17 := assump_12 assump_45
    apply False.elim assump_17
  apply Or.inl
  intro assump_21
  intro assump_22
  apply And.intro
  have assump_46 : (False → False) := by
    intro assump_28
    apply False.elim assump_28
  let assump_27 := assump_21 assump_46
  apply False.elim assump_27
  have assump_47 : (False → False) := by
    intro assump_39
    apply False.elim assump_39
  let assump_38 := assump_21 assump_47
  apply False.elim assump_38


variable (p0 p5 p4 p3 p6 p2 p7 : Prop)
theorem file67_93002 : (((((p6 ∧ p6) ∨ (p4 ∨ p0)) → False) ∧ (((p7 ∧ p7) → (p3 → False)) ∧ ((p5 ∧ p7) ∧ (p2 ∧ p5)))) → ((((False → False) ∧ (p7 ∨ p7)) → False) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_10
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          cases assump_14
          case intro assump_21 assump_22 =>
            have assump_41 : ((False → False) ∧ (p7 ∨ p7)) := by
              apply And.intro
              intro assump_35
              apply False.elim assump_35
              apply Or.inl
              exact assump_16
            let assump_34 := assump_2 assump_41
            apply False.elim assump_34


variable (p5 p3 p7 p1 p2 p0 p6 p4 : Prop)
theorem file67_93870 : (((((False ∧ p4) → (p3 ∧ p0)) ∨ ((True ∧ p5) ∧ (p7 → False))) ∨ (((p2 ∧ p5) ∨ (p7 ∧ True)) → ((True ∨ p4) → False))) ∨ ((((p2 ∨ p3) ∨ (p7 ∨ p6)) ∧ ((p0 ∧ False) → False)) ∨ (((p5 ∨ p0) ∧ (p1 ∨ False)) → ((p6 ∨ p5) ∧ (p2 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    apply False.elim assump_2
  cases assump_1
  case intro assump_6 assump_7 =>
    apply False.elim assump_6


variable (p7 p5 p6 p4 p3 : Prop)
theorem file67_94405 : ((((((p5 ∨ p4) → (p4 ∨ True)) → ((p4 ∧ p5) ∧ (p3 → False))) ∧ (((p6 ∧ p5) ∧ (False → False)) ∧ ((p7 → False) ∧ (False ∧ True)))) ∧ ((((True → False) → (p5 → False)) ∨ ((p3 ∧ p5) → (p7 → False))) → (((p4 → p6) ∨ (p4 → True)) → ((p6 → False) ∨ (p4 ∧ p3))))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_9
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                apply False.elim assump_24


variable (p0 p6 p1 p3 p4 p7 p2 p5 : Prop)
theorem file67_95253 : ((((((p3 ∧ p1) → False) → False) → (((True ∧ p0) → False) ∧ ((p7 → p5) → False))) ∧ ((((False ∧ p4) → False) → False) ∧ (((p2 ∨ p4) → False) ∨ ((False ∨ p6) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_36 : ((False ∧ p4) → False) := by
          intro assump_16
          cases assump_16
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
        let assump_15 := assump_6 assump_36
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_37 : ((False ∧ p4) → False) := by
          intro assump_28
          cases assump_28
          case intro assump_29 assump_30 =>
            apply False.elim assump_29
        let assump_27 := assump_6 assump_37
        apply False.elim assump_27


variable (p4 p5 p1 p2 p3 : Prop)
theorem file67_96230 : (((((p4 ∧ p1) ∨ (False → p5)) ∨ ((p3 → p1) ∧ (p2 ∧ p1))) → (((False → p4) → False) ∧ ((True ∧ p3) ∨ (p3 ∨ p2)))) → False) := by
  intro assump_1
  have assump_16 : (((p4 ∧ p1) ∨ (False → p5)) ∨ ((p3 → p1) ∧ (p2 ∧ p1))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_16
  let assump_8 := And.left assump_4
  have assump_17 : (False → p4) := by
    intro assump_10
    apply False.elim assump_10
  let assump_9 := assump_8 assump_17
  apply False.elim assump_9


variable (p2 p1 p4 p5 p6 : Prop)
theorem file67_96822 : ((((((p6 ∨ p4) → False) ∧ ((p4 ∧ p2) ∧ (p5 ∨ p1))) → False) → False) → False) := by
  intro assump_1
  have assump_41 : ((((p6 ∨ p4) → False) ∧ ((p4 ∧ p2) ∧ (p5 ∨ p1))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case inl assump_18 =>
            have assump_42 : (p6 ∨ p4) := by
              apply Or.inr
              exact assump_12
            let assump_25 := assump_6 assump_42
            apply False.elim assump_25
          case inr assump_19 =>
            have assump_43 : (p6 ∨ p4) := by
              apply Or.inr
              exact assump_12
            let assump_34 := assump_6 assump_43
            apply False.elim assump_34
  let assump_4 := assump_1 assump_41
  apply False.elim assump_4


variable (p3 p6 p7 p1 p4 : Prop)
theorem file67_97797 : ((((((p7 → False) ∧ (p4 ∧ p4)) ∧ ((p1 → p4) → False)) → False) ∧ ((((p4 → p6) → False) ∨ ((p1 → p3) → False)) ∧ (((True ∨ p7) ∨ (p3 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_26 : ((True ∨ p7) ∨ (p3 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_14 := assump_7 assump_26
        apply False.elim assump_14
      case inr assump_9 =>
        have assump_27 : ((True ∨ p7) ∨ (p3 → False)) := by
          apply Or.inl
          apply Or.inl
          apply True.intro
        let assump_22 := assump_7 assump_27
        apply False.elim assump_22


variable (p6 p3 p4 p5 p1 p2 p7 : Prop)
theorem file67_98650 : (((((True ∨ p4) → False) → ((p5 → p2) ∧ (True → p7))) → (((p2 ∧ p6) → (False ∧ p3)) ∧ ((p7 → p5) ∨ (p1 → p1)))) → ((((p3 ∨ p1) ∨ (True → p2)) ∧ ((False → p2) ∨ (p2 → False))) → (((p6 ∧ p6) → (False → False)) ∨ ((p6 ∧ p2) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_4
        case inl assump_11 =>
          apply Or.inl
          intro assump_17
          intro assump_18
          apply False.elim assump_18
        case inr assump_12 =>
          apply Or.inl
          intro assump_25
          intro assump_26
          apply False.elim assump_26
      case inr assump_8 =>
        cases assump_4
        case inl assump_31 =>
          apply Or.inl
          intro assump_37
          intro assump_38
          apply False.elim assump_38
        case inr assump_32 =>
          apply Or.inl
          intro assump_45
          intro assump_46
          apply False.elim assump_46
    case inr assump_6 =>
      cases assump_4
      case inl assump_51 =>
        apply Or.inl
        intro assump_57
        intro assump_58
        apply False.elim assump_58
      case inr assump_52 =>
        apply Or.inl
        intro assump_65
        intro assump_66
        apply False.elim assump_66


variable (p5 p7 p4 p6 p3 p1 p2 : Prop)
theorem file67_100080 : (((((p2 ∧ p3) ∧ (True ∧ p5)) → ((p5 ∨ p1) ∨ (False ∨ p5))) ∨ (((True → False) → (p2 ∧ p1)) → False)) ∨ ((((p5 ∨ p1) → False) ∧ ((p3 → False) → False)) ∨ (((p2 → False) → (p4 ∧ p4)) ∧ ((p7 ∧ p6) ∨ (False ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        exact assump_11


variable (p4 p7 p6 p3 p1 p2 : Prop)
theorem file67_100639 : ((((((p3 → p4) → (p6 ∨ p7)) → False) ∨ (((p2 ∧ p7) ∨ (p1 → False)) → False)) ∧ ((((False → p3) ∧ (False → False)) ∨ ((p3 ∧ p7) → (p6 ∧ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_34 : (((False → p3) ∧ (False → False)) ∨ ((p3 ∧ p7) → (p6 ∧ p3))) := by
        apply Or.inl
        apply And.intro
        intro assump_11
        apply False.elim assump_11
        intro assump_14
        apply False.elim assump_14
      let assump_10 := assump_3 assump_34
      apply False.elim assump_10
    case inr assump_5 =>
      have assump_35 : (((False → p3) ∧ (False → False)) ∨ ((p3 ∧ p7) → (p6 ∧ p3))) := by
        apply Or.inl
        apply And.intro
        intro assump_25
        apply False.elim assump_25
        intro assump_28
        apply False.elim assump_28
      let assump_24 := assump_3 assump_35
      apply False.elim assump_24


variable (p1 p3 p0 p4 p7 p2 : Prop)
theorem file67_101658 : (((((p2 ∨ p1) → (p7 ∨ False)) ∨ ((p4 → False) ∧ (p0 → True))) → (((p0 ∧ p3) ∧ (False ∧ p0)) → ((p2 → False) → False))) ∨ ((((p7 ∨ True) ∧ (p0 ∨ p4)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_7
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p1 p3 p0 p5 p7 p6 p2 p4 : Prop)
theorem file67_102166 : (((((p6 → p7) ∨ (True → False)) → ((p1 ∧ p3) ∨ (p3 → p6))) ∨ (((p1 → False) → False) → ((p5 ∧ p0) → False))) → ((((True ∨ p1) ∧ (p5 ∧ p4)) ∧ ((p4 ∨ True) → False)) → (((p2 ∨ p3) ∨ (False → p0)) ∨ ((p7 ∨ p7) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        cases assump_6
        case intro assump_11 assump_12 =>
          cases assump_1
          case inl assump_19 =>
            apply Or.inl
            apply Or.inr
            intro assump_23
            apply False.elim assump_23
          case inr assump_20 =>
            apply Or.inl
            apply Or.inr
            intro assump_28
            apply False.elim assump_28
      case inr assump_8 =>
        cases assump_6
        case intro assump_33 assump_34 =>
          cases assump_1
          case inl assump_41 =>
            apply Or.inl
            apply Or.inr
            intro assump_45
            apply False.elim assump_45
          case inr assump_42 =>
            apply Or.inl
            apply Or.inr
            intro assump_50
            apply False.elim assump_50


variable (p7 p3 p5 p2 : Prop)
theorem file67_103436 : (((((False ∧ p3) → (p7 → p7)) → False) → False) ∨ ((((p7 ∧ p2) → False) → False) ∧ (((p5 ∧ p7) ∨ (False → False)) ∨ ((p3 → False) → False)))) := by
  apply Or.inl
  intro assump_1
  have assump_16 : ((False ∧ p3) → (p7 → p7)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p0 p6 p3 p4 p5 : Prop)
theorem file67_103916 : (((((False → False) → False) ∧ ((False → False) → False)) → (((p0 ∧ True) ∨ (p0 → p0)) → False)) ∨ ((((p6 ∨ p5) ∧ (True → False)) → ((p3 ∧ p0) ∨ (False ∧ p3))) ∧ (((p0 ∨ p4) ∧ (p5 ∧ p5)) ∧ ((p4 ∨ p5) → (False ∧ False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        have assump_39 : (False → False) := by
          intro assump_18
          apply False.elim assump_18
        let assump_17 := assump_12 assump_39
        apply False.elim assump_17
  case inr assump_4 =>
    cases assump_1
    case intro assump_26 assump_27 =>
      have assump_40 : (False → False) := by
        intro assump_33
        apply False.elim assump_33
      let assump_32 := assump_27 assump_40
      apply False.elim assump_32


variable (p3 p7 p5 p0 p1 p4 : Prop)
theorem file67_104859 : ((((((p1 → False) ∧ (False ∨ p4)) ∧ ((p1 ∧ True) ∧ (p0 → False))) ∧ (((p3 → False) → False) → False)) ∧ ((((p4 ∨ p4) ∨ (p1 ∨ p5)) → False) ∧ (((True → False) ∧ (True → p5)) ∨ ((p7 ∨ True) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_9
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_7
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_3
                case intro assump_30 assump_31 =>
                  cases assump_31
                  case inl assump_34 =>
                    cases assump_34
                    case intro assump_36 assump_37 =>
                      have assump_54 : True := by
                        apply True.intro
                      let assump_44 := assump_36 assump_54
                      apply False.elim assump_44
                  case inr assump_35 =>
                    have assump_55 : (p7 ∨ True) := by
                      apply Or.inr
                      apply True.intro
                    let assump_50 := assump_35 assump_55
                    apply False.elim assump_50


variable (p6 p4 p1 p0 p5 p7 : Prop)
theorem file67_106375 : (((((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) → False) → ((((p4 ∨ p4) ∧ (True ∧ p6)) ∧ ((True → False) → (False ∧ p0))) → (((False → False) → False) ∧ ((p1 → False) ∧ (True → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          have assump_210 : (((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) := by
            intro assump_25
            apply And.intro
            intro assump_26
            apply False.elim assump_26
            cases assump_25
            case inl assump_29 =>
              apply Or.inr
              exact assump_10
            case inr assump_30 =>
              cases assump_30
              case inl assump_33 =>
                apply Or.inr
                exact assump_10
              case inr assump_34 =>
                apply Or.inr
                exact assump_10
          let assump_24 := assump_1 assump_210
          apply False.elim assump_24
      case inr assump_11 =>
        cases assump_9
        case intro assump_44 assump_45 =>
          have assump_211 : (((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) := by
            intro assump_55
            apply And.intro
            intro assump_56
            apply False.elim assump_56
            cases assump_55
            case inl assump_59 =>
              apply Or.inr
              exact assump_11
            case inr assump_60 =>
              cases assump_60
              case inl assump_63 =>
                apply Or.inr
                exact assump_11
              case inr assump_64 =>
                apply Or.inr
                exact assump_11
          let assump_54 := assump_1 assump_211
          apply False.elim assump_54
  apply And.intro
  intro assump_72
  cases assump_2
  case intro assump_75 assump_76 =>
    cases assump_75
    case intro assump_77 assump_78 =>
      cases assump_77
      case inl assump_79 =>
        cases assump_78
        case intro assump_83 assump_84 =>
          have assump_212 : (((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) := by
            intro assump_94
            apply And.intro
            intro assump_95
            apply False.elim assump_95
            cases assump_94
            case inl assump_98 =>
              apply Or.inr
              exact assump_79
            case inr assump_99 =>
              cases assump_99
              case inl assump_102 =>
                apply Or.inr
                exact assump_79
              case inr assump_103 =>
                apply Or.inr
                exact assump_79
          let assump_93 := assump_1 assump_212
          apply False.elim assump_93
      case inr assump_80 =>
        cases assump_78
        case intro assump_113 assump_114 =>
          have assump_213 : (((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) := by
            intro assump_124
            apply And.intro
            intro assump_125
            apply False.elim assump_125
            cases assump_124
            case inl assump_128 =>
              apply Or.inr
              exact assump_80
            case inr assump_129 =>
              cases assump_129
              case inl assump_132 =>
                apply Or.inr
                exact assump_80
              case inr assump_133 =>
                apply Or.inr
                exact assump_80
          let assump_123 := assump_1 assump_213
          apply False.elim assump_123
  intro assump_141
  cases assump_2
  case intro assump_144 assump_145 =>
    cases assump_144
    case intro assump_146 assump_147 =>
      cases assump_146
      case inl assump_148 =>
        cases assump_147
        case intro assump_152 assump_153 =>
          have assump_214 : (((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) := by
            intro assump_163
            apply And.intro
            intro assump_164
            apply False.elim assump_164
            cases assump_163
            case inl assump_167 =>
              apply Or.inr
              exact assump_148
            case inr assump_168 =>
              cases assump_168
              case inl assump_171 =>
                apply Or.inr
                exact assump_148
              case inr assump_172 =>
                apply Or.inr
                exact assump_148
          let assump_162 := assump_1 assump_214
          apply False.elim assump_162
      case inr assump_149 =>
        cases assump_147
        case intro assump_182 assump_183 =>
          have assump_215 : (((p0 → False) ∨ (p5 ∨ True)) → ((False → False) ∧ (p7 ∨ p4))) := by
            intro assump_193
            apply And.intro
            intro assump_194
            apply False.elim assump_194
            cases assump_193
            case inl assump_197 =>
              apply Or.inr
              exact assump_149
            case inr assump_198 =>
              cases assump_198
              case inl assump_201 =>
                apply Or.inr
                exact assump_149
              case inr assump_202 =>
                apply Or.inr
                exact assump_149
          let assump_192 := assump_1 assump_215
          apply False.elim assump_192


variable (p4 p2 p6 p1 p5 p3 : Prop)
theorem file67_111868 : (((((False → False) ∨ (True ∧ p4)) → False) → False) ∨ ((((p4 ∨ p5) → False) → False) → (((p2 ∨ p1) → (p2 → p6)) → ((p3 ∧ p4) ∨ (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((False → False) ∨ (True ∧ p4)) := by
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p4 p3 p2 p0 p5 p1 p7 : Prop)
theorem file67_112302 : (((((p5 → False) ∧ (p0 → p0)) ∧ ((p0 ∧ p4) ∧ (False ∨ p4))) → (((p5 → False) → (p7 → False)) ∧ ((True → False) → False))) → ((((p5 → False) ∧ (p3 → False)) → ((True → False) → (p0 → False))) ∨ (((p2 → False) ∧ (p2 → False)) ∨ ((p4 → False) ∨ (p1 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case intro assump_11 assump_12 =>
    have assump_23 : True := by
      apply True.intro
    let assump_19 := assump_5 assump_23
    apply False.elim assump_19


variable (p6 p2 p0 p1 p7 p5 p4 p3 : Prop)
theorem file67_112895 : (((((p2 ∨ p3) → (p3 ∧ True)) → ((True → False) → (p2 → p6))) ∨ (((p4 ∨ p7) ∧ (p5 ∨ p0)) ∨ ((p5 → p2) ∨ (p5 → p2)))) ∨ ((((p7 ∨ p4) ∧ (p4 → p6)) ∧ ((p2 → p4) → False)) ∧ (((p1 → False) ∧ (p6 → p6)) ∧ ((p1 → True) ∨ (p0 ∨ p4))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  have assump_18 : True := by
    apply True.intro
  let assump_14 := assump_2 assump_18
  apply False.elim assump_14


variable (p6 p0 p4 p3 p5 p7 : Prop)
theorem file67_113388 : (((((p3 → False) ∨ (p7 ∧ False)) → False) → False) → ((((p6 ∧ p6) ∨ (p3 → False)) ∨ ((True → p4) → (p5 ∨ p6))) ∨ (((p6 ∧ p0) → (False ∧ p6)) → False))) := by
  intro assump_5
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_8
  have assump_31 : (((p3 → False) ∨ (p7 ∧ False)) → False) := by
    intro assump_13
    cases assump_13
    case inl assump_14 =>
      have assump_32 : p3 := by
        exact assump_8
      let assump_18 := assump_14 assump_32
      apply False.elim assump_18
    case inr assump_15 =>
      cases assump_15
      case intro assump_22 assump_23 =>
        apply False.elim assump_23
  let assump_12 := assump_5 assump_31
  apply False.elim assump_12


variable (p1 p7 p2 p6 p5 p0 p4 p3 : Prop)
theorem file67_114143 : (((((p3 ∧ False) ∧ (p3 ∨ p3)) → ((True ∨ p0) ∨ (p1 → False))) → (((False → p6) ∨ (p1 ∨ p7)) ∨ ((p4 ∨ p2) ∨ (p1 ∧ True)))) ∨ ((((False → False) → False) ∧ ((p5 ∨ p1) ∧ (p5 ∧ p6))) ∨ (((False → p0) ∧ (p2 → False)) ∧ ((p1 → p5) → (p0 ∨ True))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p6 p7 p0 p4 : Prop)
theorem file67_114553 : (((((p4 ∧ False) → (p0 → False)) ∨ ((p0 → p7) ∧ (p0 ∧ p6))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p4 ∧ False) → (p0 → False)) ∨ ((p0 → p7) ∧ (p0 ∧ p6))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_10
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p0 p7 p3 p2 p5 : Prop)
theorem file67_115006 : (((((True ∧ p2) → False) → ((False → p5) ∨ (p6 → False))) → False) → ((((p3 ∨ p6) ∧ (False → True)) ∨ ((p6 → False) ∧ (p3 ∧ p7))) ∨ (((p7 ∨ False) ∨ (True ∨ True)) → ((p2 ∨ True) ∨ (False ∨ p0))))) := by
  intro assump_1
  apply Or.inr
  intro assump_18
  cases assump_18
  case inl assump_19 =>
    cases assump_19
    case inl assump_21 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_22 =>
      apply False.elim assump_22
  case inr assump_20 =>
    cases assump_20
    case inl assump_27 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_28 =>
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p6 p5 p4 p2 p7 p0 p3 : Prop)
theorem file67_115749 : (((((p5 → False) ∧ (p6 → False)) → ((False → False) → (p6 ∧ p0))) ∧ (((False → False) ∨ (p4 → p5)) ∧ ((p5 ∧ p6) → (p6 → False)))) → ((((p4 → p3) ∧ (p4 ∧ p7)) → ((p6 → False) → (p3 ∨ True))) ∧ (((p3 ∨ True) → (p5 ∨ p2)) → ((p7 ∧ False) → (p6 ∧ False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_1
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          cases assump_20
          case inl assump_22 =>
            apply Or.inr
            apply True.intro
          case inr assump_23 =>
            apply Or.inr
            apply True.intro
  intro assump_32
  intro assump_33
  apply And.intro
  cases assump_33
  case intro assump_34 assump_35 =>
    apply False.elim assump_35
  cases assump_33
  case intro assump_40 assump_41 =>
    apply False.elim assump_41


variable (p5 p3 p7 p6 p0 : Prop)
theorem file67_116792 : ((((((p6 ∧ p5) ∧ (False ∧ p5)) → False) ∨ (((p0 ∨ True) ∧ (False ∨ p7)) ∧ ((p3 → p0) → False))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p6 ∧ p5) ∧ (False ∧ p5)) → False) ∨ (((p0 ∨ True) ∧ (False ∨ p7)) ∧ ((p3 → p0) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p6 p3 p4 p0 p5 : Prop)
theorem file67_117422 : ((((((False ∧ p4) ∨ (p3 → p0)) ∧ ((p3 ∨ p0) ∧ (False → p6))) → False) ∧ ((((p5 → p5) → False) → False) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_26 : (((p5 → p5) → False) → False) := by
      intro assump_13
      have assump_27 : (p5 → p5) := by
        intro assump_17
        exact assump_17
      let assump_16 := assump_13 assump_27
      apply False.elim assump_16
    let assump_12 := assump_7 assump_26
    apply False.elim assump_12


