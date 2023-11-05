variable (p6 p5 p2 p3 p7 p4 p0 p1 : Prop)
theorem file57_50 : (((((True → p7) → (p6 ∨ True)) ∨ ((p4 → p0) → (p5 → p2))) ∨ (((p6 → False) ∧ (p1 ∨ False)) → False)) ∨ ((((p1 → False) ∨ (p3 → False)) → ((p4 ∨ p7) → (p7 → p4))) → (((p5 ∨ p0) → False) ∨ ((False ∨ p2) → (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply True.intro


variable (p5 p4 p1 : Prop)
theorem file57_423 : (((((p5 ∨ p4) ∨ (True → False)) → ((p1 ∧ p1) ∨ (p4 → p4))) → False) → False) := by
  intro assump_1
  have assump_28 : (((p5 ∨ p4) ∨ (True → False)) → ((p1 ∧ p1) ∨ (p4 → p4))) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inr
        intro assump_12
        exact assump_12
      case inr assump_9 =>
        apply Or.inr
        intro assump_17
        exact assump_17
    case inr assump_7 =>
      apply Or.inr
      intro assump_22
      exact assump_22
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p6 p3 p0 p1 p4 : Prop)
theorem file57_1091 : (((((p3 → False) → False) ∧ ((p6 → False) → (p6 ∨ False))) ∧ (((True ∨ False) → False) ∧ ((p0 ∨ p1) → False))) → ((((p1 ∧ False) ∨ (True ∨ True)) → False) ∨ (((p1 → p0) → (p4 → p6)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        cases assump_16
        case inl assump_17 =>
          cases assump_17
          case intro assump_19 assump_20 =>
            apply False.elim assump_20
        case inr assump_18 =>
          cases assump_18
          case inl assump_25 =>
            have assump_41 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_30 := assump_10 assump_41
            apply False.elim assump_30
          case inr assump_26 =>
            have assump_42 : (True ∨ False) := by
              apply Or.inl
              apply True.intro
            let assump_37 := assump_10 assump_42
            apply False.elim assump_37


variable (p7 p3 p2 p6 p0 p1 : Prop)
theorem file57_2254 : (((((True ∨ p7) ∧ (False ∧ True)) → ((p3 ∧ p0) ∨ (True → p6))) → False) → ((((p3 → p7) ∨ (p1 ∧ p7)) ∨ ((p0 → False) ∨ (p2 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      have assump_113 : (((True ∨ p7) ∧ (False ∧ True)) → ((p3 ∧ p0) ∨ (True → p6))) := by
        intro assump_12
        cases assump_12
        case intro assump_13 assump_14 =>
          cases assump_13
          case inl assump_15 =>
            cases assump_14
            case intro assump_19 assump_20 =>
              apply False.elim assump_19
          case inr assump_16 =>
            cases assump_14
            case intro assump_25 assump_26 =>
              apply False.elim assump_25
      let assump_11 := assump_1 assump_113
      apply False.elim assump_11
    case inr assump_6 =>
      cases assump_6
      case intro assump_32 assump_33 =>
        have assump_114 : (((True ∨ p7) ∧ (False ∧ True)) → ((p3 ∧ p0) ∨ (True → p6))) := by
          intro assump_41
          cases assump_41
          case intro assump_42 assump_43 =>
            cases assump_42
            case inl assump_44 =>
              cases assump_43
              case intro assump_48 assump_49 =>
                apply False.elim assump_48
            case inr assump_45 =>
              cases assump_43
              case intro assump_54 assump_55 =>
                apply False.elim assump_54
        let assump_40 := assump_1 assump_114
        apply False.elim assump_40
  case inr assump_4 =>
    cases assump_4
    case inl assump_61 =>
      have assump_115 : (((True ∨ p7) ∧ (False ∧ True)) → ((p3 ∧ p0) ∨ (True → p6))) := by
        intro assump_68
        cases assump_68
        case intro assump_69 assump_70 =>
          cases assump_69
          case inl assump_71 =>
            cases assump_70
            case intro assump_75 assump_76 =>
              apply False.elim assump_75
          case inr assump_72 =>
            cases assump_70
            case intro assump_81 assump_82 =>
              apply False.elim assump_81
      let assump_67 := assump_1 assump_115
      apply False.elim assump_67
    case inr assump_62 =>
      have assump_116 : (((True ∨ p7) ∧ (False ∧ True)) → ((p3 ∧ p0) ∨ (True → p6))) := by
        intro assump_93
        cases assump_93
        case intro assump_94 assump_95 =>
          cases assump_94
          case inl assump_96 =>
            cases assump_95
            case intro assump_100 assump_101 =>
              apply False.elim assump_100
          case inr assump_97 =>
            cases assump_95
            case intro assump_106 assump_107 =>
              apply False.elim assump_106
      let assump_92 := assump_1 assump_116
      apply False.elim assump_92


variable (p7 p0 p4 p2 p1 p3 p6 : Prop)
theorem file57_5108 : (((((p4 → False) → False) ∧ ((False ∧ p2) ∧ (p7 ∧ False))) → (((p1 ∨ p4) → (p6 ∧ p3)) ∧ ((p4 → p4) → (False ∨ p1)))) → ((((True → False) → (p1 → False)) ∧ ((p2 → True) ∨ (p7 → p1))) ∨ (((p3 → False) → (p2 ∨ p7)) → ((True ∨ p0) → (p2 → True))))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  intro assump_5
  have assump_15 : True := by
    apply True.intro
  let assump_10 := assump_4 assump_15
  apply False.elim assump_10
  apply Or.inl
  intro assump_14
  apply True.intro


variable (p4 p1 p2 p3 : Prop)
theorem file57_5667 : (((((True → False) → (p2 → p1)) ∨ ((p3 ∨ True) ∧ (p4 ∧ p4))) → False) → False) := by
  intro assump_1
  have assump_18 : (((True → False) → (p2 → p1)) ∨ ((p3 ∨ True) ∧ (p4 ∧ p4))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


theorem file57_6123 : (((((False → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → False) → False) → False) := by
    intro assump_5
    have assump_19 : (False → False) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p5 p4 p7 p6 : Prop)
theorem file57_6566 : (((((p5 ∨ p6) ∧ (p5 ∧ False)) → ((p4 ∨ p7) ∨ (p5 → False))) → False) → False) := by
  intro assump_40
  have assump_68 : (((p5 ∨ p6) ∧ (p5 ∧ False)) → ((p4 ∨ p7) ∨ (p5 → False))) := by
    intro assump_44
    cases assump_44
    case intro assump_45 assump_46 =>
      cases assump_45
      case inl assump_47 =>
        cases assump_46
        case intro assump_51 assump_52 =>
          apply False.elim assump_52
      case inr assump_48 =>
        cases assump_46
        case intro assump_59 assump_60 =>
          apply False.elim assump_60
  let assump_43 := assump_40 assump_68
  apply False.elim assump_43


variable (p7 p2 p5 p4 p3 p6 p1 : Prop)
theorem file57_7244 : (((((p3 ∧ False) → (p5 → False)) → ((p6 → False) → (p5 → True))) ∨ (((p7 ∨ p7) ∨ (p3 → False)) ∨ ((p1 → p2) → (True ∧ p4)))) ∨ ((((p4 → False) → False) ∨ ((p5 → False) ∧ (p7 → False))) ∧ (((p7 → p1) ∨ (p7 → False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply True.intro


variable (p7 p2 p1 p6 p4 p0 p5 p3 : Prop)
theorem file57_7642 : ((((((p3 ∨ p6) ∨ (p5 → p6)) ∧ ((p5 ∨ True) ∧ (p1 → False))) ∧ (((False ∧ True) ∧ (p6 → True)) ∧ ((p7 → False) ∧ (p4 → False)))) ∧ ((((p4 ∧ p3) → (p4 → p6)) ∧ ((p1 → p4) → (p7 ∨ p1))) ∧ (((p7 → p1) → (p0 ∨ p2)) ∨ ((p7 → p0) → False)))) → False) := by
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
                cases assump_5
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    cases assump_24
                    case intro assump_26 assump_27 =>
                      apply False.elim assump_26
              case inr assump_17 =>
                cases assump_5
                case intro assump_34 assump_35 =>
                  cases assump_34
                  case intro assump_36 assump_37 =>
                    cases assump_36
                    case intro assump_38 assump_39 =>
                      apply False.elim assump_38
          case inr assump_11 =>
            cases assump_7
            case intro assump_44 assump_45 =>
              cases assump_44
              case inl assump_46 =>
                cases assump_5
                case intro assump_52 assump_53 =>
                  cases assump_52
                  case intro assump_54 assump_55 =>
                    cases assump_54
                    case intro assump_56 assump_57 =>
                      apply False.elim assump_56
              case inr assump_47 =>
                cases assump_5
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case intro assump_66 assump_67 =>
                    cases assump_66
                    case intro assump_68 assump_69 =>
                      apply False.elim assump_68
        case inr assump_9 =>
          cases assump_7
          case intro assump_74 assump_75 =>
            cases assump_74
            case inl assump_76 =>
              cases assump_5
              case intro assump_82 assump_83 =>
                cases assump_82
                case intro assump_84 assump_85 =>
                  cases assump_84
                  case intro assump_86 assump_87 =>
                    apply False.elim assump_86
            case inr assump_77 =>
              cases assump_5
              case intro assump_94 assump_95 =>
                cases assump_94
                case intro assump_96 assump_97 =>
                  cases assump_96
                  case intro assump_98 assump_99 =>
                    apply False.elim assump_98


variable (p2 p4 p7 p6 p3 : Prop)
theorem file57_10624 : (((((False → p3) → (False ∨ p2)) ∧ ((p3 ∧ p6) → (p7 ∧ p3))) → False) → ((((p6 ∨ False) ∧ (p2 → p4)) ∨ ((False → p6) → False)) → (((p2 → False) → False) → ((p4 ∨ p6) ∨ (False ∨ True))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case inl assump_10 =>
        apply Or.inl
        apply Or.inr
        exact assump_10
      case inr assump_11 =>
        apply False.elim assump_11
  case inr assump_7 =>
    apply Or.inr
    apply Or.inr
    apply True.intro


variable (p4 p2 p5 p1 p7 : Prop)
theorem file57_11275 : (((((p1 → True) → False) → False) ∧ (((False ∧ True) ∧ (p7 → p2)) ∧ ((p4 → p5) → (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10


variable (p3 p7 p1 p4 p5 p0 : Prop)
theorem file57_11731 : (((((p4 → p3) → (False ∨ True)) → False) → False) ∨ ((((p1 ∧ False) → False) → ((p0 ∧ p7) ∧ (False ∨ True))) → (((True ∨ p4) → False) → ((p4 ∧ p4) ∧ (p5 → False))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p4 → p3) → (False ∨ True)) := by
    intro assump_5
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p7 p3 p4 p6 p5 p2 p1 : Prop)
theorem file57_12177 : ((((((p6 → False) → False) → ((True ∧ p0) → (p1 → False))) ∨ (((True → False) → (p3 → False)) → False)) ∧ ((((p2 → p4) → (p3 → False)) ∧ ((True ∧ False) ∧ (p6 → p1))) ∨ (((p1 → p3) ∨ (p7 → False)) ∧ ((p1 ∧ p5) ∧ (p5 ∧ False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_17
      case inr assump_9 =>
        cases assump_9
        case intro assump_22 assump_23 =>
          cases assump_22
          case inl assump_24 =>
            cases assump_23
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                cases assump_29
                case intro assump_36 assump_37 =>
                  apply False.elim assump_37
          case inr assump_25 =>
            cases assump_23
            case intro assump_44 assump_45 =>
              cases assump_44
              case intro assump_46 assump_47 =>
                cases assump_45
                case intro assump_52 assump_53 =>
                  apply False.elim assump_53
    case inr assump_5 =>
      cases assump_3
      case inl assump_60 =>
        cases assump_60
        case intro assump_62 assump_63 =>
          cases assump_63
          case intro assump_66 assump_67 =>
            cases assump_66
            case intro assump_68 assump_69 =>
              apply False.elim assump_69
      case inr assump_61 =>
        cases assump_61
        case intro assump_74 assump_75 =>
          cases assump_74
          case inl assump_76 =>
            cases assump_75
            case intro assump_80 assump_81 =>
              cases assump_80
              case intro assump_82 assump_83 =>
                cases assump_81
                case intro assump_88 assump_89 =>
                  apply False.elim assump_89
          case inr assump_77 =>
            cases assump_75
            case intro assump_96 assump_97 =>
              cases assump_96
              case intro assump_98 assump_99 =>
                cases assump_97
                case intro assump_104 assump_105 =>
                  apply False.elim assump_105


variable (p7 p5 p1 p6 p3 p0 p2 p4 : Prop)
theorem file57_14707 : ((((((p7 ∨ p1) → (p6 → False)) ∨ ((p4 ∧ p2) ∧ (p4 → False))) → (((p6 → p2) ∧ (True ∨ p1)) → False)) ∧ ((((p6 → False) ∧ (False ∨ p0)) ∧ ((p6 → False) ∨ (p5 ∧ p6))) ∨ (((p5 ∧ p0) ∧ (p5 ∧ p3)) ∧ ((p6 ∨ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            apply False.elim assump_14
          case inr assump_15 =>
            cases assump_9
            case inl assump_20 =>
              have assump_97 : (((p7 ∨ p1) → (p6 → False)) ∨ ((p4 ∧ p2) ∧ (p4 → False))) := by
                apply Or.inl
                intro assump_28
                intro assump_29
                cases assump_28
                case inl assump_32 =>
                  have assump_98 : p6 := by
                    exact assump_29
                  let assump_38 := assump_20 assump_98
                  apply False.elim assump_38
                case inr assump_33 =>
                  have assump_99 : p6 := by
                    exact assump_29
                  let assump_46 := assump_20 assump_99
                  apply False.elim assump_46
              let assump_27 := assump_2 assump_97
              have assump_100 : ((p6 → p2) ∧ (True ∨ p1)) := by
                apply And.intro
                intro assump_51
                have assump_101 : p6 := by
                  exact assump_51
                let assump_55 := assump_20 assump_101
                apply False.elim assump_55
                apply Or.inl
                apply True.intro
              let assump_50 := assump_27 assump_100
              apply False.elim assump_50
            case inr assump_21 =>
              cases assump_21
              case intro assump_62 assump_63 =>
                have assump_102 : p6 := by
                  exact assump_63
                let assump_71 := assump_10 assump_102
                apply False.elim assump_71
    case inr assump_7 =>
      cases assump_7
      case intro assump_75 assump_76 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          cases assump_77
          case intro assump_79 assump_80 =>
            cases assump_78
            case intro assump_85 assump_86 =>
              have assump_103 : (p6 ∨ p3) := by
                apply Or.inr
                exact assump_86
              let assump_93 := assump_76 assump_103
              apply False.elim assump_93


variable (p0 p6 p2 p3 : Prop)
theorem file57_17365 : ((((((p0 ∧ p2) ∨ (p0 ∧ p6)) ∨ ((True → False) → False)) ∨ (((p3 ∨ True) ∧ (p0 ∧ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p0 ∧ p2) ∨ (p0 ∧ p6)) ∨ ((True → False) → False)) ∨ (((p3 ∨ True) ∧ (p0 ∧ p0)) → False)) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    have assump_16 : True := by
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p0 p2 p5 p4 p1 : Prop)
theorem file57_17921 : ((((((p3 → False) → False) ∨ ((False ∨ p1) → False)) → False) ∧ ((((True ∧ p5) → (p0 → False)) ∨ ((True ∧ p2) ∨ (p4 → False))) ∧ (((False ∧ p3) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_55 : ((False ∧ p3) → False) := by
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
        let assump_14 := assump_7 assump_55
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_23 =>
          cases assump_23
          case intro assump_25 assump_26 =>
            have assump_56 : ((False ∧ p3) → False) := by
              intro assump_34
              cases assump_34
              case intro assump_35 assump_36 =>
                apply False.elim assump_35
            let assump_33 := assump_7 assump_56
            apply False.elim assump_33
        case inr assump_24 =>
          have assump_57 : ((False ∧ p3) → False) := by
            intro assump_47
            cases assump_47
            case intro assump_48 assump_49 =>
              apply False.elim assump_48
          let assump_46 := assump_7 assump_57
          apply False.elim assump_46


variable (p2 p0 p1 p3 p6 : Prop)
theorem file57_19354 : (((((p1 → p2) → (False → p3)) → False) → False) ∧ ((((True → False) → (p6 → False)) ∧ ((p2 → False) → False)) → (((p6 ∧ False) → False) ∨ ((p0 → False) → (p0 → p3))))) := by
  apply And.intro
  intro assump_19
  have assump_44 : ((p1 → p2) → (False → p3)) := by
    intro assump_23
    intro assump_24
    apply False.elim assump_24
  let assump_22 := assump_19 assump_44
  apply False.elim assump_22
  intro assump_30
  cases assump_30
  case intro assump_31 assump_32 =>
    apply Or.inl
    intro assump_37
    cases assump_37
    case intro assump_38 assump_39 =>
      apply False.elim assump_39


variable (p0 p3 p7 p1 p5 p2 p4 : Prop)
theorem file57_20018 : (((((p5 → False) → (p7 → p7)) → False) → (((p4 ∨ p0) → False) ∧ ((False ∧ p2) ∧ (p4 ∧ p5)))) ∨ ((((False → False) ∧ (p2 → False)) ∧ ((p3 ∧ False) ∧ (p2 ∧ True))) ∨ (((True ∨ p1) ∧ (p5 ∧ p2)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_81 : ((p5 → False) → (p7 → p7)) := by
      intro assump_10
      intro assump_11
      exact assump_11
    let assump_9 := assump_1 assump_81
    apply False.elim assump_9
  case inr assump_4 =>
    have assump_82 : ((p5 → False) → (p7 → p7)) := by
      intro assump_24
      intro assump_25
      exact assump_25
    let assump_23 := assump_1 assump_82
    apply False.elim assump_23
  apply And.intro
  apply And.intro
  have assump_83 : ((p5 → False) → (p7 → p7)) := by
    intro assump_36
    intro assump_37
    exact assump_37
  let assump_35 := assump_1 assump_83
  apply False.elim assump_35
  have assump_84 : ((p5 → False) → (p7 → p7)) := by
    intro assump_48
    intro assump_49
    exact assump_49
  let assump_47 := assump_1 assump_84
  apply False.elim assump_47
  apply And.intro
  have assump_85 : ((p5 → False) → (p7 → p7)) := by
    intro assump_60
    intro assump_61
    exact assump_61
  let assump_59 := assump_1 assump_85
  apply False.elim assump_59
  have assump_86 : ((p5 → False) → (p7 → p7)) := by
    intro assump_72
    intro assump_73
    exact assump_73
  let assump_71 := assump_1 assump_86
  apply False.elim assump_71


variable (p2 p4 p0 p3 p6 p1 p7 p5 : Prop)
theorem file57_21572 : ((((((p4 ∧ True) ∨ (p2 ∧ p1)) ∨ ((p3 → p6) ∨ (p4 ∧ p2))) ∨ (((True → p2) ∧ (p5 → True)) → False)) ∧ ((((p0 ∧ p4) ∨ (p3 → False)) ∧ ((p7 → p2) ∧ (p4 ∧ False))) ∧ (((p5 ∨ p1) → False) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case intro assump_10 assump_11 =>
            cases assump_3
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case inl assump_20 =>
                  cases assump_20
                  case intro assump_22 assump_23 =>
                    cases assump_19
                    case intro assump_28 assump_29 =>
                      cases assump_29
                      case intro assump_32 assump_33 =>
                        apply False.elim assump_33
                case inr assump_21 =>
                  cases assump_19
                  case intro assump_40 assump_41 =>
                    cases assump_41
                    case intro assump_44 assump_45 =>
                      apply False.elim assump_45
        case inr assump_9 =>
          cases assump_9
          case intro assump_50 assump_51 =>
            cases assump_3
            case intro assump_56 assump_57 =>
              cases assump_56
              case intro assump_58 assump_59 =>
                cases assump_58
                case inl assump_60 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    cases assump_59
                    case intro assump_68 assump_69 =>
                      cases assump_69
                      case intro assump_72 assump_73 =>
                        apply False.elim assump_73
                case inr assump_61 =>
                  cases assump_59
                  case intro assump_80 assump_81 =>
                    cases assump_81
                    case intro assump_84 assump_85 =>
                      apply False.elim assump_85
      case inr assump_7 =>
        cases assump_7
        case inl assump_90 =>
          cases assump_3
          case intro assump_94 assump_95 =>
            cases assump_94
            case intro assump_96 assump_97 =>
              cases assump_96
              case inl assump_98 =>
                cases assump_98
                case intro assump_100 assump_101 =>
                  cases assump_97
                  case intro assump_106 assump_107 =>
                    cases assump_107
                    case intro assump_110 assump_111 =>
                      apply False.elim assump_111
              case inr assump_99 =>
                cases assump_97
                case intro assump_118 assump_119 =>
                  cases assump_119
                  case intro assump_122 assump_123 =>
                    apply False.elim assump_123
        case inr assump_91 =>
          cases assump_91
          case intro assump_128 assump_129 =>
            cases assump_3
            case intro assump_134 assump_135 =>
              cases assump_134
              case intro assump_136 assump_137 =>
                cases assump_136
                case inl assump_138 =>
                  cases assump_138
                  case intro assump_140 assump_141 =>
                    cases assump_137
                    case intro assump_146 assump_147 =>
                      cases assump_147
                      case intro assump_150 assump_151 =>
                        apply False.elim assump_151
                case inr assump_139 =>
                  cases assump_137
                  case intro assump_158 assump_159 =>
                    cases assump_159
                    case intro assump_162 assump_163 =>
                      apply False.elim assump_163
    case inr assump_5 =>
      cases assump_3
      case intro assump_170 assump_171 =>
        cases assump_170
        case intro assump_172 assump_173 =>
          cases assump_172
          case inl assump_174 =>
            cases assump_174
            case intro assump_176 assump_177 =>
              cases assump_173
              case intro assump_182 assump_183 =>
                cases assump_183
                case intro assump_186 assump_187 =>
                  apply False.elim assump_187
          case inr assump_175 =>
            cases assump_173
            case intro assump_194 assump_195 =>
              cases assump_195
              case intro assump_198 assump_199 =>
                apply False.elim assump_199


variable (p7 p6 p3 p5 : Prop)
theorem file57_26357 : (((((p3 ∨ True) ∨ (p5 ∨ True)) ∨ ((p6 ∧ True) ∧ (False ∨ p7))) → False) → False) := by
  intro assump_1
  have assump_8 : (((p3 ∨ True) ∨ (p5 ∨ True)) ∨ ((p6 ∧ True) ∧ (False ∨ p7))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p3 p1 p7 p4 : Prop)
theorem file57_26736 : ((((((False → False) ∧ (p7 → False)) ∧ ((p1 → False) → (p4 → False))) ∨ (((p7 → False) ∨ (p3 → False)) → False)) ∧ ((((p1 ∨ p3) → False) → ((p7 ∧ True) ∨ (p1 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          have assump_38 : (((p1 ∨ p3) → False) → ((p7 ∧ True) ∨ (p1 → True))) := by
            intro assump_19
            apply Or.inr
            intro assump_22
            apply True.intro
          let assump_18 := assump_3 assump_38
          apply False.elim assump_18
    case inr assump_5 =>
      have assump_39 : (((p1 ∨ p3) → False) → ((p7 ∧ True) ∨ (p1 → True))) := by
        intro assump_31
        apply Or.inr
        intro assump_34
        apply True.intro
      let assump_30 := assump_3 assump_39
      apply False.elim assump_30


variable (p5 p4 p1 p6 : Prop)
theorem file57_27770 : ((((((True ∧ False) ∧ (p5 → False)) ∨ ((p6 → False) ∧ (p1 ∧ p5))) ∧ (((False ∨ p6) → (p6 ∧ p6)) → False)) ∧ ((((p1 ∨ False) ∨ (p4 → False)) ∨ ((p4 → False) → False)) → False)) → False) := by
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
            apply False.elim assump_11
      case inr assump_7 =>
        cases assump_7
        case intro assump_16 assump_17 =>
          cases assump_17
          case intro assump_20 assump_21 =>
            have assump_34 : (((p1 ∨ False) ∨ (p4 → False)) ∨ ((p4 → False) → False)) := by
              apply Or.inl
              apply Or.inl
              apply Or.inl
              exact assump_20
            let assump_30 := assump_3 assump_34
            apply False.elim assump_30


variable (p0 p7 p5 p3 p1 p6 : Prop)
theorem file57_28815 : ((((((p0 → False) → (p0 → False)) → False) ∧ (((True ∧ False) ∧ (p1 ∧ False)) → ((False ∨ p6) → False))) ∨ ((((p3 ∧ p6) → (p0 → p5)) → ((True → False) → (p7 ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_42 : ((p0 → False) → (p0 → False)) := by
        intro assump_12
        intro assump_13
        have assump_43 : p0 := by
          exact assump_13
        let assump_18 := assump_12 assump_43
        apply False.elim assump_18
      let assump_11 := assump_4 assump_42
      apply False.elim assump_11
  case inr assump_3 =>
    have assump_44 : (((p3 ∧ p6) → (p0 → p5)) → ((True → False) → (p7 ∨ False))) := by
      intro assump_28
      intro assump_29
      have assump_45 : True := by
        apply True.intro
      let assump_35 := assump_29 assump_45
      apply False.elim assump_35
    let assump_27 := assump_3 assump_44
    apply False.elim assump_27


variable (p0 p1 p2 p7 p4 : Prop)
theorem file57_29859 : ((((((p0 ∨ p2) → (p7 ∨ p1)) → ((p1 → p1) ∨ (p4 → False))) ∨ (((p0 ∨ p2) ∧ (p2 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 ∨ p2) → (p7 ∨ p1)) → ((p1 → p1) ∨ (p4 → False))) ∨ (((p0 ∨ p2) ∧ (p2 → False)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p2 p0 : Prop)
theorem file57_30326 : (((((p0 ∨ p6) ∨ (True ∨ False)) ∨ ((True → p2) ∨ (False ∨ p6))) → False) → False) := by
  intro assump_25
  have assump_32 : (((p0 ∨ p6) ∨ (True ∨ False)) ∨ ((True → p2) ∨ (False ∨ p6))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_28 := assump_25 assump_32
  apply False.elim assump_28


variable (p1 p6 p2 p7 p5 p3 p4 : Prop)
theorem file57_30722 : (((((p7 → False) ∨ (p2 → p2)) ∧ ((p1 ∧ p3) → (p6 ∨ p7))) → (((p3 ∧ p5) → (p7 ∧ p6)) → False)) → ((((p4 ∨ True) ∧ (False ∧ p1)) → False) ∨ (((p5 ∨ True) ∨ (p2 → False)) → ((False ∨ p7) ∨ (p7 → p4))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        apply False.elim assump_11
    case inr assump_8 =>
      cases assump_6
      case intro assump_17 assump_18 =>
        apply False.elim assump_17


variable (p1 p7 : Prop)
theorem file57_31337 : ((((((p1 ∨ p7) ∨ (p7 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 ∨ p7) ∨ (p7 → False)) → False) → False) := by
    intro assump_5
    have assump_24 : ((p1 ∨ p7) ∨ (p7 → False)) := by
      apply Or.inr
      intro assump_9
      have assump_25 : ((p1 ∨ p7) ∨ (p7 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_5 assump_25
      apply False.elim assump_13
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p4 p5 p0 : Prop)
theorem file57_31996 : ((((((p0 ∧ p4) ∧ (True → p5)) → ((p0 → False) → (False → p2))) ∨ (((p5 ∧ p0) → False) ∨ ((p5 → False) → (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p0 ∧ p4) ∧ (True → p5)) → ((p0 → False) → (False → p2))) ∨ (((p5 ∧ p0) → False) ∨ ((p5 → False) → (p2 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p2 p6 p7 p1 : Prop)
theorem file57_32523 : (((((p1 → p7) → (False → p6)) ∨ ((p2 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : (((p1 → p7) → (False → p6)) ∨ ((p2 → False) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply False.elim assump_6
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p2 p0 : Prop)
theorem file57_32897 : (((((p2 ∨ p0) → False) → ((True ∧ p0) → False)) → False) → False) := by
  intro assump_9
  have assump_30 : (((p2 ∨ p0) → False) → ((True ∧ p0) → False)) := by
    intro assump_13
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      have assump_31 : (p2 ∨ p0) := by
        apply Or.inr
        exact assump_16
      let assump_23 := assump_13 assump_31
      apply False.elim assump_23
  let assump_12 := assump_9 assump_30
  apply False.elim assump_12


variable (p6 p2 p5 p7 p4 : Prop)
theorem file57_33439 : ((((((p4 ∧ False) ∧ (p6 ∨ p4)) ∧ ((p2 → False) → False)) ∨ (((p6 → p7) → (True → False)) → ((p5 ∨ True) ∧ (p7 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p4 ∧ False) ∧ (p6 ∨ p4)) ∧ ((p2 → False) → False)) ∨ (((p6 → p7) → (True → False)) → ((p5 ∨ True) ∧ (p7 ∨ True)))) := by
    apply Or.inr
    intro assump_5
    apply And.intro
    apply Or.inr
    apply True.intro
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p6 p2 p7 p4 p3 p5 p0 : Prop)
theorem file57_34005 : (((((p2 ∧ p6) ∧ (p3 → False)) ∨ ((True → False) → False)) ∨ (((p7 → False) → False) ∧ ((p4 → False) → (p5 ∧ p2)))) ∨ ((((False → False) → False) → False) ∧ (((False ∧ p5) ∧ (p7 ∨ p2)) ∨ ((True → p3) → (False ∧ p0))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  have assump_8 : True := by
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p2 p7 p0 p6 : Prop)
theorem file57_34462 : ((((((True ∨ p4) → False) → ((p7 → p2) ∨ (p0 ∨ p0))) ∨ (((p4 ∨ p6) ∨ (False ∨ True)) ∧ ((p4 ∨ p2) ∨ (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_19 : ((((True ∨ p4) → False) → ((p7 → p2) ∨ (p0 ∨ p0))) ∨ (((p4 ∨ p6) ∨ (False ∨ True)) ∧ ((p4 ∨ p2) ∨ (p6 → False)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_20 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_12 := assump_5 assump_20
    apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p2 p5 p4 p0 p7 p6 : Prop)
theorem file57_35110 : (((((True → p4) ∧ (p7 ∧ p2)) → ((False → False) → (p7 ∨ p1))) ∧ (((p7 ∧ False) ∧ (p6 ∧ p2)) ∧ ((p5 → False) → (False → p5)))) → ((((p0 → False) ∧ (False → True)) ∨ ((False ∨ p0) → (p5 ∨ p0))) → (((False ∨ False) → False) → ((p2 → False) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_2
  case inl assump_9 =>
    cases assump_9
    case intro assump_11 assump_12 =>
      cases assump_1
      case intro assump_17 assump_18 =>
        cases assump_18
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            cases assump_23
            case intro assump_25 assump_26 =>
              apply False.elim assump_26
  case inr assump_10 =>
    cases assump_1
    case intro assump_33 assump_34 =>
      cases assump_34
      case intro assump_37 assump_38 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          cases assump_39
          case intro assump_41 assump_42 =>
            apply False.elim assump_42


variable (p7 p1 p6 p4 p0 p2 p3 : Prop)
theorem file57_36223 : (((((p2 → True) ∨ (p6 ∨ p3)) → False) → (((p1 ∨ p6) ∧ (p4 → False)) ∨ ((False ∨ True) → False))) ∨ ((((p0 ∨ p4) ∧ (False ∨ p7)) → False) ∧ (((p7 ∧ p3) ∨ (p0 → p4)) ∨ ((p0 → False) ∨ (p3 → p4))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply False.elim assump_5
  case inr assump_6 =>
    have assump_16 : ((p2 → True) ∨ (p6 ∨ p3)) := by
      apply Or.inl
      intro assump_12
      apply True.intro
    let assump_11 := assump_1 assump_16
    apply False.elim assump_11


variable (p7 p3 p2 p5 p6 p1 p4 p0 : Prop)
theorem file57_36836 : ((((((p2 → p3) ∨ (p6 ∧ p6)) ∨ ((True ∨ True) → False)) ∧ (((p6 → False) ∧ (p6 → False)) ∧ ((p4 → p1) ∧ (p0 ∧ p3)))) ∧ ((((p7 → p5) → (False → False)) ∨ ((p3 ∨ p7) ∧ (True → False))) ∧ (((False → p3) → False) ∧ ((p1 → False) ∨ (p7 → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_12 assump_13 =>
            cases assump_12
            case intro assump_14 assump_15 =>
              cases assump_13
              case intro assump_20 assump_21 =>
                cases assump_21
                case intro assump_24 assump_25 =>
                  cases assump_3
                  case intro assump_30 assump_31 =>
                    cases assump_30
                    case inl assump_32 =>
                      cases assump_31
                      case intro assump_36 assump_37 =>
                        cases assump_37
                        case inl assump_40 =>
                          have assump_365 : (False → p3) := by
                            intro assump_46
                            apply False.elim assump_46
                          let assump_45 := assump_36 assump_365
                          apply False.elim assump_45
                        case inr assump_41 =>
                          have assump_366 : (False → p3) := by
                            intro assump_56
                            apply False.elim assump_56
                          let assump_55 := assump_36 assump_366
                          apply False.elim assump_55
                    case inr assump_33 =>
                      cases assump_33
                      case intro assump_62 assump_63 =>
                        cases assump_62
                        case inl assump_64 =>
                          cases assump_31
                          case intro assump_70 assump_71 =>
                            cases assump_71
                            case inl assump_74 =>
                              have assump_367 : (False → p3) := by
                                intro assump_80
                                apply False.elim assump_80
                              let assump_79 := assump_70 assump_367
                              apply False.elim assump_79
                            case inr assump_75 =>
                              have assump_368 : (False → p3) := by
                                intro assump_90
                                apply False.elim assump_90
                              let assump_89 := assump_70 assump_368
                              apply False.elim assump_89
                        case inr assump_65 =>
                          cases assump_31
                          case intro assump_100 assump_101 =>
                            cases assump_101
                            case inl assump_104 =>
                              have assump_369 : (False → p3) := by
                                intro assump_110
                                apply False.elim assump_110
                              let assump_109 := assump_100 assump_369
                              apply False.elim assump_109
                            case inr assump_105 =>
                              have assump_370 : (False → p3) := by
                                intro assump_121
                                apply False.elim assump_121
                              let assump_120 := assump_100 assump_370
                              apply False.elim assump_120
        case inr assump_9 =>
          cases assump_9
          case intro assump_127 assump_128 =>
            cases assump_5
            case intro assump_133 assump_134 =>
              cases assump_133
              case intro assump_135 assump_136 =>
                cases assump_134
                case intro assump_141 assump_142 =>
                  cases assump_142
                  case intro assump_145 assump_146 =>
                    cases assump_3
                    case intro assump_151 assump_152 =>
                      cases assump_151
                      case inl assump_153 =>
                        cases assump_152
                        case intro assump_157 assump_158 =>
                          cases assump_158
                          case inl assump_161 =>
                            have assump_371 : (False → p3) := by
                              intro assump_167
                              apply False.elim assump_167
                            let assump_166 := assump_157 assump_371
                            apply False.elim assump_166
                          case inr assump_162 =>
                            have assump_372 : (False → p3) := by
                              intro assump_177
                              apply False.elim assump_177
                            let assump_176 := assump_157 assump_372
                            apply False.elim assump_176
                      case inr assump_154 =>
                        cases assump_154
                        case intro assump_183 assump_184 =>
                          cases assump_183
                          case inl assump_185 =>
                            cases assump_152
                            case intro assump_191 assump_192 =>
                              cases assump_192
                              case inl assump_195 =>
                                have assump_373 : (False → p3) := by
                                  intro assump_201
                                  apply False.elim assump_201
                                let assump_200 := assump_191 assump_373
                                apply False.elim assump_200
                              case inr assump_196 =>
                                have assump_374 : (False → p3) := by
                                  intro assump_211
                                  apply False.elim assump_211
                                let assump_210 := assump_191 assump_374
                                apply False.elim assump_210
                          case inr assump_186 =>
                            cases assump_152
                            case intro assump_221 assump_222 =>
                              cases assump_222
                              case inl assump_225 =>
                                have assump_375 : (False → p3) := by
                                  intro assump_231
                                  apply False.elim assump_231
                                let assump_230 := assump_221 assump_375
                                apply False.elim assump_230
                              case inr assump_226 =>
                                have assump_376 : (False → p3) := by
                                  intro assump_242
                                  apply False.elim assump_242
                                let assump_241 := assump_221 assump_376
                                apply False.elim assump_241
      case inr assump_7 =>
        cases assump_5
        case intro assump_250 assump_251 =>
          cases assump_250
          case intro assump_252 assump_253 =>
            cases assump_251
            case intro assump_258 assump_259 =>
              cases assump_259
              case intro assump_262 assump_263 =>
                cases assump_3
                case intro assump_268 assump_269 =>
                  cases assump_268
                  case inl assump_270 =>
                    cases assump_269
                    case intro assump_274 assump_275 =>
                      cases assump_275
                      case inl assump_278 =>
                        have assump_377 : (False → p3) := by
                          intro assump_284
                          apply False.elim assump_284
                        let assump_283 := assump_274 assump_377
                        apply False.elim assump_283
                      case inr assump_279 =>
                        have assump_378 : (False → p3) := by
                          intro assump_294
                          apply False.elim assump_294
                        let assump_293 := assump_274 assump_378
                        apply False.elim assump_293
                  case inr assump_271 =>
                    cases assump_271
                    case intro assump_300 assump_301 =>
                      cases assump_300
                      case inl assump_302 =>
                        cases assump_269
                        case intro assump_308 assump_309 =>
                          cases assump_309
                          case inl assump_312 =>
                            have assump_379 : (False → p3) := by
                              intro assump_318
                              apply False.elim assump_318
                            let assump_317 := assump_308 assump_379
                            apply False.elim assump_317
                          case inr assump_313 =>
                            have assump_380 : (False → p3) := by
                              intro assump_328
                              apply False.elim assump_328
                            let assump_327 := assump_308 assump_380
                            apply False.elim assump_327
                      case inr assump_303 =>
                        cases assump_269
                        case intro assump_338 assump_339 =>
                          cases assump_339
                          case inl assump_342 =>
                            have assump_381 : (False → p3) := by
                              intro assump_348
                              apply False.elim assump_348
                            let assump_347 := assump_338 assump_381
                            apply False.elim assump_347
                          case inr assump_343 =>
                            have assump_382 : (False → p3) := by
                              intro assump_359
                              apply False.elim assump_359
                            let assump_358 := assump_338 assump_382
                            apply False.elim assump_358


variable (p3 p0 p7 p5 p4 p2 : Prop)
theorem file57_47274 : (((((p2 → p7) → False) ∨ ((p0 → False) ∨ (p3 → False))) ∧ (((p4 ∧ p5) ∨ (True ∨ p5)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_32 : ((p4 ∧ p5) ∨ (True ∨ p5)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_32
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_14 =>
        have assump_33 : ((p4 ∧ p5) ∨ (True ∨ p5)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_20 := assump_3 assump_33
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_34 : ((p4 ∧ p5) ∨ (True ∨ p5)) := by
          apply Or.inr
          apply Or.inl
          apply True.intro
        let assump_28 := assump_3 assump_34
        apply False.elim assump_28


variable (p2 p5 p1 p3 p0 p4 p6 p7 : Prop)
theorem file57_48279 : (((((p3 → False) ∧ (p1 ∨ True)) → ((p1 ∧ p4) ∨ (p7 ∨ True))) ∨ (((p5 ∨ p6) → False) → False)) ∨ ((((p3 ∧ True) ∨ (False → False)) ∧ ((True ∧ p2) ∧ (False → False))) → (((p5 → p5) → (p0 → False)) ∧ ((p6 → p7) → (p3 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inr
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      apply Or.inr
      apply Or.inr
      apply True.intro


variable (p2 p6 p3 : Prop)
theorem file57_48852 : (((((p2 ∧ p3) → (False → p2)) → ((p6 → False) → (False → False))) → False) → False) := by
  intro assump_1
  have assump_13 : (((p2 ∧ p3) → (False → p2)) → ((p6 → False) → (False → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p1 p3 p6 p4 p0 p2 : Prop)
theorem file57_49260 : (((((True → p0) ∧ (True → p2)) → ((p4 ∧ p6) → False)) ∧ (((p3 → False) ∧ (p4 → True)) ∧ ((p1 → p1) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_23 : (p1 → p1) := by
          intro assump_17
          exact assump_17
        let assump_16 := assump_7 assump_23
        apply False.elim assump_16


variable (p2 p1 p0 p3 p5 p6 : Prop)
theorem file57_49799 : ((((((p0 ∧ p3) ∧ (p6 → p1)) ∧ ((p6 ∧ p5) → False)) → (((p3 → False) → (False → False)) ∧ ((True → p2) → (p5 → p0)))) → False) → False) := by
  intro assump_10
  have assump_42 : ((((p0 ∧ p3) ∧ (p6 → p1)) ∧ ((p6 ∧ p5) → False)) → (((p3 → False) → (False → False)) ∧ ((True → p2) → (p5 → p0)))) := by
    intro assump_14
    apply And.intro
    intro assump_15
    intro assump_16
    apply False.elim assump_16
    intro assump_19
    intro assump_20
    cases assump_14
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          exact assump_29
  let assump_13 := assump_10 assump_42
  apply False.elim assump_13


variable (p0 p6 p3 p7 p1 : Prop)
theorem file57_50586 : (((((p6 ∨ True) → (p7 ∧ p1)) → ((p0 ∧ p7) → (p0 ∧ p3))) ∧ (((False → False) ∨ (True → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((False → False) ∨ (True → False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p6 p4 p5 p0 p2 p1 : Prop)
theorem file57_51036 : (((((True ∧ p6) ∧ (False ∨ True)) ∧ ((p2 ∧ p2) → (p5 → False))) ∧ (((False ∧ False) → False) → ((p0 ∨ p6) → False))) → ((((p1 ∨ p1) ∧ (p4 → False)) → False) ∧ (((True ∨ p4) → False) → False))) := by
  intro assump_17
  apply And.intro
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_17
      case intro assump_27 assump_28 =>
        cases assump_27
        case intro assump_29 assump_30 =>
          cases assump_29
          case intro assump_31 assump_32 =>
            cases assump_31
            case intro assump_33 assump_34 =>
              cases assump_32
              case inl assump_39 =>
                apply False.elim assump_39
              case inr assump_40 =>
                have assump_130 : ((False ∧ False) → False) := by
                  intro assump_50
                  cases assump_50
                  case intro assump_51 assump_52 =>
                    apply False.elim assump_51
                let assump_49 := assump_28 assump_130
                have assump_131 : (p0 ∨ p6) := by
                  apply Or.inr
                  exact assump_34
                let assump_55 := assump_49 assump_131
                apply False.elim assump_55
    case inr assump_22 =>
      cases assump_17
      case intro assump_63 assump_64 =>
        cases assump_63
        case intro assump_65 assump_66 =>
          cases assump_65
          case intro assump_67 assump_68 =>
            cases assump_67
            case intro assump_69 assump_70 =>
              cases assump_68
              case inl assump_75 =>
                apply False.elim assump_75
              case inr assump_76 =>
                have assump_132 : ((False ∧ False) → False) := by
                  intro assump_86
                  cases assump_86
                  case intro assump_87 assump_88 =>
                    apply False.elim assump_87
                let assump_85 := assump_64 assump_132
                have assump_133 : (p0 ∨ p6) := by
                  apply Or.inr
                  exact assump_70
                let assump_91 := assump_85 assump_133
                apply False.elim assump_91
  intro assump_95
  cases assump_17
  case intro assump_98 assump_99 =>
    cases assump_98
    case intro assump_100 assump_101 =>
      cases assump_100
      case intro assump_102 assump_103 =>
        cases assump_102
        case intro assump_104 assump_105 =>
          cases assump_103
          case inl assump_110 =>
            apply False.elim assump_110
          case inr assump_111 =>
            have assump_134 : ((False ∧ False) → False) := by
              intro assump_121
              cases assump_121
              case intro assump_122 assump_123 =>
                apply False.elim assump_122
            let assump_120 := assump_99 assump_134
            have assump_135 : (p0 ∨ p6) := by
              apply Or.inr
              exact assump_105
            let assump_126 := assump_120 assump_135
            apply False.elim assump_126


variable (p6 p7 p2 : Prop)
theorem file57_54162 : ((((((p6 ∨ p7) ∨ (p6 ∨ False)) ∧ ((True ∨ p7) ∧ (False ∧ p2))) → False) → False) → False) := by
  intro assump_1
  have assump_73 : ((((p6 ∨ p7) ∨ (p6 ∨ False)) ∧ ((True ∨ p7) ∧ (False ∧ p2))) → False) := by
    intro assump_5
    cases assump_5
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
                apply False.elim assump_20
            case inr assump_17 =>
              cases assump_15
              case intro assump_26 assump_27 =>
                apply False.elim assump_26
        case inr assump_11 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_32
            case inl assump_34 =>
              cases assump_33
              case intro assump_38 assump_39 =>
                apply False.elim assump_38
            case inr assump_35 =>
              cases assump_33
              case intro assump_44 assump_45 =>
                apply False.elim assump_44
      case inr assump_9 =>
        cases assump_9
        case inl assump_48 =>
          cases assump_7
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
        case inr assump_49 =>
          apply False.elim assump_49
  let assump_4 := assump_1 assump_73
  apply False.elim assump_4


variable (p1 p3 p0 p2 p7 p5 p4 : Prop)
theorem file57_56071 : ((((((True → False) → False) ∨ ((p0 → False) ∧ (p2 → p5))) → (((True ∨ p7) → False) ∧ ((p2 → p2) ∨ (p1 → p4)))) ∧ ((((p2 → p3) ∧ (p7 ∨ p1)) → False) ∧ (((False → True) → (False ∧ p1)) ∧ ((p0 ∨ True) ∧ (True → p7))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_14
          case inl assump_16 =>
            have assump_43 : (False → True) := by
              intro assump_26
              apply True.intro
            let assump_25 := assump_10 assump_43
            let assump_27 := And.left assump_25
            apply False.elim assump_27
          case inr assump_17 =>
            have assump_44 : (False → True) := by
              intro assump_38
              apply True.intro
            let assump_37 := assump_10 assump_44
            let assump_39 := And.left assump_37
            apply False.elim assump_39


variable (p6 p2 p0 p1 p7 : Prop)
theorem file57_57194 : ((((((False ∧ p6) → (p6 → False)) ∨ ((p0 ∨ p7) ∧ (p1 ∧ p1))) ∨ (((p1 → False) → (False → p6)) → ((p2 ∧ p0) → False))) → False) → False) := by
  intro assump_1
  have assump_16 : ((((False ∧ p6) → (p6 → False)) ∨ ((p0 ∨ p7) ∧ (p1 ∧ p1))) ∨ (((p1 → False) → (False → p6)) → ((p2 ∧ p0) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p5 p4 p0 p1 p6 p3 p7 : Prop)
theorem file57_57782 : (((((p6 ∧ p4) ∧ (p6 → p1)) → False) → (((p4 ∧ p4) → False) → ((p5 ∨ False) → False))) → ((((p1 → False) ∧ (True ∧ False)) → ((True → p1) → False)) ∨ (((False → p7) ∨ (p5 → False)) ∧ ((False ∧ True) → (p0 → p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      apply False.elim assump_13


variable (p3 p2 p7 p1 p6 p4 p0 : Prop)
theorem file57_58272 : (((((True ∨ p7) → (True → p0)) ∨ ((False → False) ∨ (p1 → p1))) → (((p1 ∨ p1) → False) → ((True ∨ p2) ∨ (p3 → p4)))) ∨ ((((p0 ∧ p6) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    apply Or.inl
    apply True.intro
  case inr assump_6 =>
    cases assump_6
    case inl assump_9 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_10 =>
      apply Or.inl
      apply Or.inl
      apply True.intro


variable (p0 p2 p4 p1 p6 p5 p7 : Prop)
theorem file57_58860 : (((((p5 ∨ True) → False) → False) ∨ (((p1 ∧ p0) ∨ (p7 → p4)) → ((p2 → p2) → False))) ∧ ((((True → False) ∧ (p6 → False)) → False) ∨ (((True ∧ p4) ∨ (p2 ∨ p5)) ∧ ((p7 → False) ∨ (p2 ∨ p1))))) := by
  apply And.intro
  apply Or.inl
  intro assump_13
  have assump_32 : (p5 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_16 := assump_13 assump_32
  apply False.elim assump_16
  apply Or.inl
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    have assump_33 : True := by
      apply True.intro
    let assump_28 := assump_21 assump_33
    apply False.elim assump_28


variable (p4 : Prop)
theorem file57_59510 : (((((p4 → p4) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((p4 → p4) → False) → False) := by
    intro assump_5
    have assump_19 : (p4 → p4) := by
      intro assump_9
      exact assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p2 p0 p6 p1 p7 p4 p5 p3 : Prop)
theorem file57_59936 : (((((p2 ∧ p6) ∨ (False → p3)) → ((p0 ∧ True) → False)) ∧ (((False → p4) → (False → p0)) → False)) → ((((p1 ∧ p2) ∧ (p7 ∨ p7)) → ((p7 ∨ p7) → False)) ∧ (((p1 ∨ p0) ∨ (p6 ∨ p5)) → False))) := by
  intro assump_9
  apply And.intro
  intro assump_10
  intro assump_11
  cases assump_11
  case inl assump_12 =>
    cases assump_10
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_17
        case inl assump_24 =>
          cases assump_9
          case intro assump_28 assump_29 =>
            have assump_173 : ((False → p4) → (False → p0)) := by
              intro assump_35
              intro assump_36
              apply False.elim assump_36
            let assump_34 := assump_29 assump_173
            apply False.elim assump_34
        case inr assump_25 =>
          cases assump_9
          case intro assump_44 assump_45 =>
            have assump_174 : ((False → p4) → (False → p0)) := by
              intro assump_51
              intro assump_52
              apply False.elim assump_52
            let assump_50 := assump_45 assump_174
            apply False.elim assump_50
  case inr assump_13 =>
    cases assump_10
    case intro assump_60 assump_61 =>
      cases assump_60
      case intro assump_62 assump_63 =>
        cases assump_61
        case inl assump_68 =>
          cases assump_9
          case intro assump_72 assump_73 =>
            have assump_175 : ((False → p4) → (False → p0)) := by
              intro assump_79
              intro assump_80
              apply False.elim assump_80
            let assump_78 := assump_73 assump_175
            apply False.elim assump_78
        case inr assump_69 =>
          cases assump_9
          case intro assump_88 assump_89 =>
            have assump_176 : ((False → p4) → (False → p0)) := by
              intro assump_95
              intro assump_96
              apply False.elim assump_96
            let assump_94 := assump_89 assump_176
            apply False.elim assump_94
  intro assump_102
  cases assump_102
  case inl assump_103 =>
    cases assump_103
    case inl assump_105 =>
      cases assump_9
      case intro assump_109 assump_110 =>
        have assump_177 : ((False → p4) → (False → p0)) := by
          intro assump_116
          intro assump_117
          apply False.elim assump_117
        let assump_115 := assump_110 assump_177
        apply False.elim assump_115
    case inr assump_106 =>
      cases assump_9
      case intro assump_125 assump_126 =>
        have assump_178 : ((False → p4) → (False → p0)) := by
          intro assump_132
          intro assump_133
          apply False.elim assump_133
        let assump_131 := assump_126 assump_178
        apply False.elim assump_131
  case inr assump_104 =>
    cases assump_104
    case inl assump_139 =>
      cases assump_9
      case intro assump_143 assump_144 =>
        have assump_179 : ((False → p4) → (False → p0)) := by
          intro assump_150
          intro assump_151
          apply False.elim assump_151
        let assump_149 := assump_144 assump_179
        apply False.elim assump_149
    case inr assump_140 =>
      cases assump_9
      case intro assump_159 assump_160 =>
        have assump_180 : ((False → p4) → (False → p0)) := by
          intro assump_166
          intro assump_167
          apply False.elim assump_167
        let assump_165 := assump_160 assump_180
        apply False.elim assump_165


variable (p6 p0 p3 p1 p7 p5 p2 p4 : Prop)
theorem file57_63482 : (((((p7 ∧ False) → False) → ((p3 → p3) → (p3 ∧ p2))) → False) → ((((True ∧ p5) ∧ (p5 → False)) ∨ ((p1 ∨ p5) → (False → False))) ∨ (((p1 ∧ p6) → False) ∨ ((p6 ∨ p4) ∧ (p0 → False))))) := by
  intro assump_7
  apply Or.inl
  apply Or.inr
  intro assump_10
  intro assump_11
  apply False.elim assump_11


variable (p5 p4 p0 p3 p2 p1 p7 p6 : Prop)
theorem file57_63849 : (((((False → p5) ∨ (p7 → p0)) ∧ ((p7 ∨ p3) → False)) → (((False → p2) → (p0 → p5)) ∧ ((p1 → p2) → (p3 ∨ p4)))) → ((((False ∧ p3) ∧ (p2 ∨ p0)) ∨ ((False ∧ p1) → (p6 ∨ p6))) ∨ (((p5 → False) → (True → p0)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply False.elim assump_5


variable (p7 p4 p5 p0 p3 p2 p6 : Prop)
theorem file57_64278 : (((((False → False) ∧ (p4 ∧ p0)) ∨ ((p2 → False) → False)) → False) → ((((p6 → p4) ∧ (p7 → False)) ∧ ((True ∨ p3) → (p2 → p4))) → (((p0 ∨ p5) ∧ (p2 ∧ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case intro assump_10 assump_11 =>
        cases assump_2
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            have assump_76 : (((False → False) ∧ (p4 ∧ p0)) ∨ ((p2 → False) → False)) := by
              apply Or.inr
              intro assump_32
              have assump_77 : p2 := by
                exact assump_10
              let assump_35 := assump_32 assump_77
              apply False.elim assump_35
            let assump_28 := assump_1 assump_76
            apply False.elim assump_28
    case inr assump_7 =>
      cases assump_5
      case intro assump_44 assump_45 =>
        cases assump_2
        case intro assump_50 assump_51 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            have assump_78 : (((False → False) ∧ (p4 ∧ p0)) ∨ ((p2 → False) → False)) := by
              apply Or.inr
              intro assump_66
              have assump_79 : p2 := by
                exact assump_44
              let assump_69 := assump_66 assump_79
              apply False.elim assump_69
            let assump_62 := assump_1 assump_78
            apply False.elim assump_62


variable (p7 p4 p2 p5 p1 p6 : Prop)
theorem file57_65873 : ((((((False ∨ p6) ∨ (False → False)) ∨ ((p4 → False) → False)) → False) ∧ ((((p2 → False) ∨ (False → False)) ∨ ((p5 → False) ∨ (p7 ∧ p5))) ∧ (((p1 ∨ p5) ∨ (p7 ∧ p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_65 : (((False ∨ p6) ∨ (False → False)) ∨ ((p4 → False) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_2 assump_65
          apply False.elim assump_18
        case inr assump_11 =>
          have assump_66 : (((False ∨ p6) ∨ (False → False)) ∨ ((p4 → False) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_32
            apply False.elim assump_32
          let assump_31 := assump_2 assump_66
          apply False.elim assump_31
      case inr assump_9 =>
        cases assump_9
        case inl assump_38 =>
          have assump_67 : (((False ∨ p6) ∨ (False → False)) ∨ ((p4 → False) → False)) := by
            apply Or.inl
            apply Or.inr
            intro assump_47
            apply False.elim assump_47
          let assump_46 := assump_2 assump_67
          apply False.elim assump_46
        case inr assump_39 =>
          cases assump_39
          case intro assump_53 assump_54 =>
            have assump_68 : ((p1 ∨ p5) ∨ (p7 ∧ p6)) := by
              apply Or.inl
              apply Or.inr
              exact assump_54
            let assump_61 := assump_7 assump_68
            apply False.elim assump_61


variable (p2 p3 p0 p7 p4 p1 : Prop)
theorem file57_67668 : (((((True → False) ∨ (p4 ∨ p2)) → ((p0 → True) ∨ (p2 → p1))) → (((True ∨ p3) ∨ (False ∧ p7)) → False)) → False) := by
  intro assump_7
  have assump_29 : (((True → False) ∨ (p4 ∨ p2)) → ((p0 → True) ∨ (p2 → p1))) := by
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      apply Or.inl
      intro assump_16
      apply True.intro
    case inr assump_13 =>
      cases assump_13
      case inl assump_17 =>
        apply Or.inl
        intro assump_21
        apply True.intro
      case inr assump_18 =>
        apply Or.inl
        intro assump_24
        apply True.intro
  let assump_10 := assump_7 assump_29
  have assump_30 : ((True ∨ p3) ∨ (False ∧ p7)) := by
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_25 := assump_10 assump_30
  apply False.elim assump_25


variable (p7 p1 p5 p4 p3 p2 p6 : Prop)
theorem file57_68539 : ((((((p1 ∧ p4) ∨ (p1 → False)) ∧ ((p7 ∨ p6) ∧ (p3 ∨ True))) ∨ (((p1 ∨ p4) → False) ∧ ((True → p5) → False))) ∧ ((((p7 ∧ p5) ∨ (p1 ∧ p4)) ∧ ((p5 → p5) → False)) ∧ (((False → False) → False) ∧ ((p2 → False) ∨ (p4 → False))))) → False) := by
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case inl assump_21 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_23
        case inl assump_25 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            cases assump_24
            case intro assump_33 assump_34 =>
              cases assump_33
              case inl assump_35 =>
                cases assump_34
                case inl assump_39 =>
                  cases assump_20
                  case intro assump_43 assump_44 =>
                    cases assump_43
                    case intro assump_45 assump_46 =>
                      cases assump_45
                      case inl assump_47 =>
                        cases assump_47
                        case intro assump_49 assump_50 =>
                          cases assump_44
                          case intro assump_57 assump_58 =>
                            cases assump_58
                            case inl assump_61 =>
                              have assump_695 : (False → False) := by
                                intro assump_67
                                apply False.elim assump_67
                              let assump_66 := assump_57 assump_695
                              apply False.elim assump_66
                            case inr assump_62 =>
                              have assump_696 : p4 := by
                                exact assump_28
                              let assump_75 := assump_62 assump_696
                              apply False.elim assump_75
                      case inr assump_48 =>
                        cases assump_48
                        case intro assump_79 assump_80 =>
                          cases assump_44
                          case intro assump_87 assump_88 =>
                            cases assump_88
                            case inl assump_91 =>
                              have assump_697 : (False → False) := by
                                intro assump_97
                                apply False.elim assump_97
                              let assump_96 := assump_87 assump_697
                              apply False.elim assump_96
                            case inr assump_92 =>
                              have assump_698 : p4 := by
                                exact assump_80
                              let assump_105 := assump_92 assump_698
                              apply False.elim assump_105
                case inr assump_40 =>
                  cases assump_20
                  case intro assump_111 assump_112 =>
                    cases assump_111
                    case intro assump_113 assump_114 =>
                      cases assump_113
                      case inl assump_115 =>
                        cases assump_115
                        case intro assump_117 assump_118 =>
                          cases assump_112
                          case intro assump_125 assump_126 =>
                            cases assump_126
                            case inl assump_129 =>
                              have assump_699 : (False → False) := by
                                intro assump_135
                                apply False.elim assump_135
                              let assump_134 := assump_125 assump_699
                              apply False.elim assump_134
                            case inr assump_130 =>
                              have assump_700 : p4 := by
                                exact assump_28
                              let assump_143 := assump_130 assump_700
                              apply False.elim assump_143
                      case inr assump_116 =>
                        cases assump_116
                        case intro assump_147 assump_148 =>
                          cases assump_112
                          case intro assump_155 assump_156 =>
                            cases assump_156
                            case inl assump_159 =>
                              have assump_701 : (False → False) := by
                                intro assump_165
                                apply False.elim assump_165
                              let assump_164 := assump_155 assump_701
                              apply False.elim assump_164
                            case inr assump_160 =>
                              have assump_702 : p4 := by
                                exact assump_148
                              let assump_173 := assump_160 assump_702
                              apply False.elim assump_173
              case inr assump_36 =>
                cases assump_34
                case inl assump_179 =>
                  cases assump_20
                  case intro assump_183 assump_184 =>
                    cases assump_183
                    case intro assump_185 assump_186 =>
                      cases assump_185
                      case inl assump_187 =>
                        cases assump_187
                        case intro assump_189 assump_190 =>
                          cases assump_184
                          case intro assump_197 assump_198 =>
                            cases assump_198
                            case inl assump_201 =>
                              have assump_703 : (False → False) := by
                                intro assump_207
                                apply False.elim assump_207
                              let assump_206 := assump_197 assump_703
                              apply False.elim assump_206
                            case inr assump_202 =>
                              have assump_704 : p4 := by
                                exact assump_28
                              let assump_215 := assump_202 assump_704
                              apply False.elim assump_215
                      case inr assump_188 =>
                        cases assump_188
                        case intro assump_219 assump_220 =>
                          cases assump_184
                          case intro assump_227 assump_228 =>
                            cases assump_228
                            case inl assump_231 =>
                              have assump_705 : (False → False) := by
                                intro assump_237
                                apply False.elim assump_237
                              let assump_236 := assump_227 assump_705
                              apply False.elim assump_236
                            case inr assump_232 =>
                              have assump_706 : p4 := by
                                exact assump_220
                              let assump_245 := assump_232 assump_706
                              apply False.elim assump_245
                case inr assump_180 =>
                  cases assump_20
                  case intro assump_251 assump_252 =>
                    cases assump_251
                    case intro assump_253 assump_254 =>
                      cases assump_253
                      case inl assump_255 =>
                        cases assump_255
                        case intro assump_257 assump_258 =>
                          cases assump_252
                          case intro assump_265 assump_266 =>
                            cases assump_266
                            case inl assump_269 =>
                              have assump_707 : (False → False) := by
                                intro assump_275
                                apply False.elim assump_275
                              let assump_274 := assump_265 assump_707
                              apply False.elim assump_274
                            case inr assump_270 =>
                              have assump_708 : p4 := by
                                exact assump_28
                              let assump_283 := assump_270 assump_708
                              apply False.elim assump_283
                      case inr assump_256 =>
                        cases assump_256
                        case intro assump_287 assump_288 =>
                          cases assump_252
                          case intro assump_295 assump_296 =>
                            cases assump_296
                            case inl assump_299 =>
                              have assump_709 : (False → False) := by
                                intro assump_305
                                apply False.elim assump_305
                              let assump_304 := assump_295 assump_709
                              apply False.elim assump_304
                            case inr assump_300 =>
                              have assump_710 : p4 := by
                                exact assump_288
                              let assump_313 := assump_300 assump_710
                              apply False.elim assump_313
        case inr assump_26 =>
          cases assump_24
          case intro assump_319 assump_320 =>
            cases assump_319
            case inl assump_321 =>
              cases assump_320
              case inl assump_325 =>
                cases assump_20
                case intro assump_329 assump_330 =>
                  cases assump_329
                  case intro assump_331 assump_332 =>
                    cases assump_331
                    case inl assump_333 =>
                      cases assump_333
                      case intro assump_335 assump_336 =>
                        cases assump_330
                        case intro assump_343 assump_344 =>
                          cases assump_344
                          case inl assump_347 =>
                            have assump_711 : (False → False) := by
                              intro assump_353
                              apply False.elim assump_353
                            let assump_352 := assump_343 assump_711
                            apply False.elim assump_352
                          case inr assump_348 =>
                            have assump_712 : (False → False) := by
                              intro assump_363
                              apply False.elim assump_363
                            let assump_362 := assump_343 assump_712
                            apply False.elim assump_362
                    case inr assump_334 =>
                      cases assump_334
                      case intro assump_369 assump_370 =>
                        cases assump_330
                        case intro assump_377 assump_378 =>
                          cases assump_378
                          case inl assump_381 =>
                            have assump_713 : (False → False) := by
                              intro assump_387
                              apply False.elim assump_387
                            let assump_386 := assump_377 assump_713
                            apply False.elim assump_386
                          case inr assump_382 =>
                            have assump_714 : p4 := by
                              exact assump_370
                            let assump_395 := assump_382 assump_714
                            apply False.elim assump_395
              case inr assump_326 =>
                cases assump_20
                case intro assump_401 assump_402 =>
                  cases assump_401
                  case intro assump_403 assump_404 =>
                    cases assump_403
                    case inl assump_405 =>
                      cases assump_405
                      case intro assump_407 assump_408 =>
                        cases assump_402
                        case intro assump_415 assump_416 =>
                          cases assump_416
                          case inl assump_419 =>
                            have assump_715 : (False → False) := by
                              intro assump_425
                              apply False.elim assump_425
                            let assump_424 := assump_415 assump_715
                            apply False.elim assump_424
                          case inr assump_420 =>
                            have assump_716 : (False → False) := by
                              intro assump_435
                              apply False.elim assump_435
                            let assump_434 := assump_415 assump_716
                            apply False.elim assump_434
                    case inr assump_406 =>
                      cases assump_406
                      case intro assump_441 assump_442 =>
                        cases assump_402
                        case intro assump_449 assump_450 =>
                          cases assump_450
                          case inl assump_453 =>
                            have assump_717 : (False → False) := by
                              intro assump_459
                              apply False.elim assump_459
                            let assump_458 := assump_449 assump_717
                            apply False.elim assump_458
                          case inr assump_454 =>
                            have assump_718 : p4 := by
                              exact assump_442
                            let assump_467 := assump_454 assump_718
                            apply False.elim assump_467
            case inr assump_322 =>
              cases assump_320
              case inl assump_473 =>
                cases assump_20
                case intro assump_477 assump_478 =>
                  cases assump_477
                  case intro assump_479 assump_480 =>
                    cases assump_479
                    case inl assump_481 =>
                      cases assump_481
                      case intro assump_483 assump_484 =>
                        cases assump_478
                        case intro assump_491 assump_492 =>
                          cases assump_492
                          case inl assump_495 =>
                            have assump_719 : (False → False) := by
                              intro assump_501
                              apply False.elim assump_501
                            let assump_500 := assump_491 assump_719
                            apply False.elim assump_500
                          case inr assump_496 =>
                            have assump_720 : (False → False) := by
                              intro assump_511
                              apply False.elim assump_511
                            let assump_510 := assump_491 assump_720
                            apply False.elim assump_510
                    case inr assump_482 =>
                      cases assump_482
                      case intro assump_517 assump_518 =>
                        cases assump_478
                        case intro assump_525 assump_526 =>
                          cases assump_526
                          case inl assump_529 =>
                            have assump_721 : (False → False) := by
                              intro assump_535
                              apply False.elim assump_535
                            let assump_534 := assump_525 assump_721
                            apply False.elim assump_534
                          case inr assump_530 =>
                            have assump_722 : p4 := by
                              exact assump_518
                            let assump_543 := assump_530 assump_722
                            apply False.elim assump_543
              case inr assump_474 =>
                cases assump_20
                case intro assump_549 assump_550 =>
                  cases assump_549
                  case intro assump_551 assump_552 =>
                    cases assump_551
                    case inl assump_553 =>
                      cases assump_553
                      case intro assump_555 assump_556 =>
                        cases assump_550
                        case intro assump_563 assump_564 =>
                          cases assump_564
                          case inl assump_567 =>
                            have assump_723 : (False → False) := by
                              intro assump_573
                              apply False.elim assump_573
                            let assump_572 := assump_563 assump_723
                            apply False.elim assump_572
                          case inr assump_568 =>
                            have assump_724 : (False → False) := by
                              intro assump_583
                              apply False.elim assump_583
                            let assump_582 := assump_563 assump_724
                            apply False.elim assump_582
                    case inr assump_554 =>
                      cases assump_554
                      case intro assump_589 assump_590 =>
                        cases assump_550
                        case intro assump_597 assump_598 =>
                          cases assump_598
                          case inl assump_601 =>
                            have assump_725 : (False → False) := by
                              intro assump_607
                              apply False.elim assump_607
                            let assump_606 := assump_597 assump_725
                            apply False.elim assump_606
                          case inr assump_602 =>
                            have assump_726 : p4 := by
                              exact assump_590
                            let assump_615 := assump_602 assump_726
                            apply False.elim assump_615
    case inr assump_22 =>
      cases assump_22
      case intro assump_619 assump_620 =>
        cases assump_20
        case intro assump_625 assump_626 =>
          cases assump_625
          case intro assump_627 assump_628 =>
            cases assump_627
            case inl assump_629 =>
              cases assump_629
              case intro assump_631 assump_632 =>
                cases assump_626
                case intro assump_639 assump_640 =>
                  cases assump_640
                  case inl assump_643 =>
                    have assump_727 : (False → False) := by
                      intro assump_649
                      apply False.elim assump_649
                    let assump_648 := assump_639 assump_727
                    apply False.elim assump_648
                  case inr assump_644 =>
                    have assump_728 : (False → False) := by
                      intro assump_659
                      apply False.elim assump_659
                    let assump_658 := assump_639 assump_728
                    apply False.elim assump_658
            case inr assump_630 =>
              cases assump_630
              case intro assump_665 assump_666 =>
                cases assump_626
                case intro assump_673 assump_674 =>
                  cases assump_674
                  case inl assump_677 =>
                    have assump_729 : (False → False) := by
                      intro assump_683
                      apply False.elim assump_683
                    let assump_682 := assump_673 assump_729
                    apply False.elim assump_682
                  case inr assump_678 =>
                    have assump_730 : p4 := by
                      exact assump_666
                    let assump_691 := assump_678 assump_730
                    apply False.elim assump_691


variable (p6 p5 p0 p4 : Prop)
theorem file57_88513 : (((((p5 ∨ True) ∨ (p0 → False)) → False) ∧ (((p4 → True) ∨ (p6 ∧ p6)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p4 → True) ∨ (p6 ∧ p6)) := by
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p7 p0 p1 p6 p5 p2 p4 : Prop)
theorem file57_88924 : ((((((p4 ∧ p1) ∨ (p1 → False)) ∧ ((p1 ∨ p7) → (True ∨ p5))) ∨ (((p4 ∨ p1) ∨ (p1 → False)) ∧ ((False ∨ p4) → False))) ∧ ((((p6 ∧ False) ∧ (p2 ∧ p1)) ∧ ((p2 → True) ∨ (p1 ∧ p0))) ∧ (((True → p0) → False) → False))) → False) := by
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
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_20
                case intro assump_22 assump_23 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    apply False.elim assump_25
        case inr assump_9 =>
          cases assump_3
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              cases assump_36
              case intro assump_38 assump_39 =>
                cases assump_38
                case intro assump_40 assump_41 =>
                  apply False.elim assump_41
    case inr assump_5 =>
      cases assump_5
      case intro assump_46 assump_47 =>
        cases assump_46
        case inl assump_48 =>
          cases assump_48
          case inl assump_50 =>
            cases assump_3
            case intro assump_56 assump_57 =>
              cases assump_56
              case intro assump_58 assump_59 =>
                cases assump_58
                case intro assump_60 assump_61 =>
                  cases assump_60
                  case intro assump_62 assump_63 =>
                    apply False.elim assump_63
          case inr assump_51 =>
            cases assump_3
            case intro assump_72 assump_73 =>
              cases assump_72
              case intro assump_74 assump_75 =>
                cases assump_74
                case intro assump_76 assump_77 =>
                  cases assump_76
                  case intro assump_78 assump_79 =>
                    apply False.elim assump_79
        case inr assump_49 =>
          cases assump_3
          case intro assump_88 assump_89 =>
            cases assump_88
            case intro assump_90 assump_91 =>
              cases assump_90
              case intro assump_92 assump_93 =>
                cases assump_92
                case intro assump_94 assump_95 =>
                  apply False.elim assump_95


variable (p5 p3 p2 p0 p4 p6 : Prop)
theorem file57_91587 : (((((p6 → False) ∨ (True ∨ p0)) → False) → False) → ((((p4 → p4) ∧ (False ∧ p0)) → ((False → p4) → False)) ∨ (((p4 → False) → (p5 → False)) → ((p2 ∧ p2) ∨ (p3 → False))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      apply False.elim assump_12


variable (p6 p3 p4 p5 p2 p1 p7 : Prop)
theorem file57_92035 : (((((p3 → False) → False) → False) → (((p1 ∧ p7) ∧ (p3 ∧ p6)) → ((p2 → False) ∨ (p7 ∨ p7)))) ∨ ((((p5 → True) → False) → False) → (((p7 ∧ p3) → (p5 → False)) ∨ ((p4 ∧ False) ∨ (p5 ∧ True))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_4
      case intro assump_11 assump_12 =>
        apply Or.inl
        intro assump_19
        have assump_34 : ((p3 → False) → False) := by
          intro assump_24
          have assump_35 : p3 := by
            exact assump_11
          let assump_27 := assump_24 assump_35
          apply False.elim assump_27
        let assump_23 := assump_1 assump_34
        apply False.elim assump_23


variable (p3 p0 p6 p2 p4 p1 : Prop)
theorem file57_92861 : ((((((p0 → False) ∨ (p6 ∨ p1)) ∧ ((False → p4) → False)) → (((p3 → False) → False) ∨ ((p3 → p0) ∨ (p2 → p3)))) → False) → False) := by
  intro assump_1
  have assump_60 : ((((p0 → False) ∨ (p6 ∨ p1)) ∧ ((False → p4) → False)) → (((p3 → False) → False) ∨ ((p3 → p0) ∨ (p2 → p3)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        intro assump_14
        have assump_61 : (False → p4) := by
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_7 assump_61
        apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case inl assump_25 =>
          apply Or.inl
          intro assump_31
          have assump_62 : (False → p4) := by
            intro assump_36
            apply False.elim assump_36
          let assump_35 := assump_7 assump_62
          apply False.elim assump_35
        case inr assump_26 =>
          apply Or.inl
          intro assump_46
          have assump_63 : (False → p4) := by
            intro assump_51
            apply False.elim assump_51
          let assump_50 := assump_7 assump_63
          apply False.elim assump_50
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p6 p0 p1 p7 p3 p5 : Prop)
theorem file57_94225 : (((((p0 → False) ∧ (p5 ∧ p1)) → ((p1 ∧ False) → (p3 → False))) ∨ (((p5 ∨ p6) ∧ (p5 → p7)) ∨ ((p6 ∨ p1) ∧ (p7 ∧ True)))) ∨ ((((p5 → False) → False) ∨ ((p3 → False) → (p7 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p5 p4 p0 p6 p1 p2 : Prop)
theorem file57_94643 : (((((p2 → False) → False) → ((False → p1) ∨ (p5 → False))) → False) → ((((p2 ∨ p4) → (p6 → p4)) ∧ ((p4 → p0) → (False → p6))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_21 : (((p2 → False) → False) → ((False → p1) ∨ (p5 → False))) := by
      intro assump_12
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
    let assump_11 := assump_1 assump_21
    apply False.elim assump_11


variable (p2 p1 p4 p0 p6 p5 p3 p7 : Prop)
theorem file57_95187 : (((((False ∧ p6) → (p7 → p1)) ∨ ((p2 ∧ p0) ∨ (p1 ∨ p0))) ∧ (((p7 → False) ∨ (p1 ∨ p2)) ∧ ((p1 → False) ∧ (p6 → False)))) → ((((p2 → False) → (p4 → p2)) ∧ ((p5 ∨ p2) → False)) → (((False ∧ p3) ∨ (p2 → p3)) → ((p4 ∧ p3) → (p7 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    cases assump_3
    case inl assump_14 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_16
    case inr assump_15 =>
      cases assump_2
      case intro assump_22 assump_23 =>
        cases assump_1
        case intro assump_28 assump_29 =>
          cases assump_28
          case inl assump_30 =>
            cases assump_29
            case intro assump_34 assump_35 =>
              cases assump_34
              case inl assump_36 =>
                cases assump_35
                case intro assump_40 assump_41 =>
                  have assump_241 : p7 := by
                    exact assump_5
                  let assump_48 := assump_36 assump_241
                  apply False.elim assump_48
              case inr assump_37 =>
                cases assump_37
                case inl assump_52 =>
                  cases assump_35
                  case intro assump_56 assump_57 =>
                    have assump_242 : p1 := by
                      exact assump_52
                    let assump_63 := assump_56 assump_242
                    apply False.elim assump_63
                case inr assump_53 =>
                  cases assump_35
                  case intro assump_69 assump_70 =>
                    have assump_243 : (p5 ∨ p2) := by
                      apply Or.inr
                      exact assump_53
                    let assump_79 := assump_23 assump_243
                    apply False.elim assump_79
          case inr assump_31 =>
            cases assump_31
            case inl assump_83 =>
              cases assump_83
              case intro assump_85 assump_86 =>
                cases assump_29
                case intro assump_91 assump_92 =>
                  cases assump_91
                  case inl assump_93 =>
                    cases assump_92
                    case intro assump_97 assump_98 =>
                      have assump_244 : p7 := by
                        exact assump_5
                      let assump_105 := assump_93 assump_244
                      apply False.elim assump_105
                  case inr assump_94 =>
                    cases assump_94
                    case inl assump_109 =>
                      cases assump_92
                      case intro assump_113 assump_114 =>
                        have assump_245 : p1 := by
                          exact assump_109
                        let assump_120 := assump_113 assump_245
                        apply False.elim assump_120
                    case inr assump_110 =>
                      cases assump_92
                      case intro assump_126 assump_127 =>
                        have assump_246 : (p5 ∨ p2) := by
                          apply Or.inr
                          exact assump_110
                        let assump_137 := assump_23 assump_246
                        apply False.elim assump_137
            case inr assump_84 =>
              cases assump_84
              case inl assump_141 =>
                cases assump_29
                case intro assump_145 assump_146 =>
                  cases assump_145
                  case inl assump_147 =>
                    cases assump_146
                    case intro assump_151 assump_152 =>
                      have assump_247 : p1 := by
                        exact assump_141
                      let assump_158 := assump_151 assump_247
                      apply False.elim assump_158
                  case inr assump_148 =>
                    cases assump_148
                    case inl assump_162 =>
                      cases assump_146
                      case intro assump_166 assump_167 =>
                        have assump_248 : p1 := by
                          exact assump_162
                        let assump_173 := assump_166 assump_248
                        apply False.elim assump_173
                    case inr assump_163 =>
                      cases assump_146
                      case intro assump_179 assump_180 =>
                        have assump_249 : p1 := by
                          exact assump_141
                        let assump_186 := assump_179 assump_249
                        apply False.elim assump_186
              case inr assump_142 =>
                cases assump_29
                case intro assump_192 assump_193 =>
                  cases assump_192
                  case inl assump_194 =>
                    cases assump_193
                    case intro assump_198 assump_199 =>
                      have assump_250 : p7 := by
                        exact assump_5
                      let assump_206 := assump_194 assump_250
                      apply False.elim assump_206
                  case inr assump_195 =>
                    cases assump_195
                    case inl assump_210 =>
                      cases assump_193
                      case intro assump_214 assump_215 =>
                        have assump_251 : p1 := by
                          exact assump_210
                        let assump_221 := assump_214 assump_251
                        apply False.elim assump_221
                    case inr assump_211 =>
                      cases assump_193
                      case intro assump_227 assump_228 =>
                        have assump_252 : (p5 ∨ p2) := by
                          apply Or.inr
                          exact assump_211
                        let assump_237 := assump_23 assump_252
                        apply False.elim assump_237


variable (p6 p7 p0 p1 p5 p2 p4 : Prop)
theorem file57_101205 : (((((True → False) → (p6 → p6)) → False) ∧ (((False ∧ p7) → False) ∧ ((p5 ∧ p0) ∨ (False → False)))) → ((((p7 → p7) ∨ (p0 → p1)) → ((False ∧ p0) ∨ (p4 ∨ True))) ∨ (((True ∨ True) ∨ (True ∧ p2)) ∨ ((p2 → False) ∧ (p5 ∧ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case inl assump_19 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
          case inr assump_20 =>
            apply Or.inr
            apply Or.inr
            apply True.intro
      case inr assump_11 =>
        apply Or.inl
        intro assump_27
        cases assump_27
        case inl assump_28 =>
          apply Or.inr
          apply Or.inr
          apply True.intro
        case inr assump_29 =>
          apply Or.inr
          apply Or.inr
          apply True.intro


variable (p2 p6 p3 p1 p4 p5 p0 p7 : Prop)
theorem file57_102341 : (((((p3 ∧ p4) → False) ∧ ((p6 ∨ p4) ∨ (p1 ∧ p2))) ∧ (((True → p4) → (p3 → p3)) ∧ ((True ∧ True) → False))) → ((((True → p7) ∧ (p4 ∨ p6)) ∨ ((p5 ∨ p6) → False)) ∧ (((p5 ∨ p6) ∨ (p5 ∨ p1)) ∨ ((p0 → False) ∧ (p1 → False))))) := by
  intro assump_1
  apply And.intro
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
            apply Or.inl
            apply And.intro
            intro assump_20
            have assump_132 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_23 := assump_15 assump_132
            apply False.elim assump_23
            apply Or.inr
            exact assump_10
        case inr assump_11 =>
          cases assump_3
          case intro assump_29 assump_30 =>
            apply Or.inl
            apply And.intro
            intro assump_35
            have assump_133 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_38 := assump_30 assump_133
            apply False.elim assump_38
            apply Or.inl
            exact assump_11
      case inr assump_9 =>
        cases assump_9
        case intro assump_42 assump_43 =>
          cases assump_3
          case intro assump_48 assump_49 =>
            apply Or.inr
            intro assump_61
            cases assump_61
            case inl assump_62 =>
              have assump_134 : (True ∧ True) := by
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_67 := assump_49 assump_134
              apply False.elim assump_67
            case inr assump_63 =>
              have assump_135 : (True ∧ True) := by
                apply And.intro
                apply True.intro
                apply True.intro
              let assump_74 := assump_49 assump_135
              apply False.elim assump_74
  cases assump_1
  case intro assump_78 assump_79 =>
    cases assump_78
    case intro assump_80 assump_81 =>
      cases assump_81
      case inl assump_84 =>
        cases assump_84
        case inl assump_86 =>
          cases assump_79
          case intro assump_90 assump_91 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            exact assump_86
        case inr assump_87 =>
          cases assump_79
          case intro assump_98 assump_99 =>
            apply Or.inr
            apply And.intro
            intro assump_104
            have assump_136 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_108 := assump_99 assump_136
            apply False.elim assump_108
            intro assump_112
            have assump_137 : (True ∧ True) := by
              apply And.intro
              apply True.intro
              apply True.intro
            let assump_116 := assump_99 assump_137
            apply False.elim assump_116
      case inr assump_85 =>
        cases assump_85
        case intro assump_120 assump_121 =>
          cases assump_79
          case intro assump_126 assump_127 =>
            apply Or.inl
            apply Or.inr
            apply Or.inr
            exact assump_120


variable (p3 p5 p6 p0 p2 p4 p1 p7 : Prop)
theorem file57_105908 : (((((p4 ∧ p4) ∨ (p1 ∨ p5)) ∨ ((p3 → p6) ∨ (p5 ∨ False))) → (((p0 ∧ p3) ∨ (p3 ∨ p0)) ∨ ((p3 → p7) → (False → False)))) ∨ ((((False ∧ p0) ∧ (p7 → False)) ∨ ((p2 ∧ p4) ∧ (p4 → p3))) ∧ (((False ∧ p3) → False) ∨ ((True → False) ∨ (True → p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply Or.inr
        intro assump_12
        intro assump_13
        apply False.elim assump_13
    case inr assump_5 =>
      cases assump_5
      case inl assump_16 =>
        apply Or.inr
        intro assump_20
        intro assump_21
        apply False.elim assump_21
      case inr assump_17 =>
        apply Or.inr
        intro assump_26
        intro assump_27
        apply False.elim assump_27
  case inr assump_3 =>
    cases assump_3
    case inl assump_30 =>
      apply Or.inr
      intro assump_34
      intro assump_35
      apply False.elim assump_35
    case inr assump_31 =>
      cases assump_31
      case inl assump_38 =>
        apply Or.inr
        intro assump_42
        intro assump_43
        apply False.elim assump_43
      case inr assump_39 =>
        apply False.elim assump_39


theorem file57_107175 : ((((((False ∧ False) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_20 : ((((False ∧ False) → False) → False) → False) := by
    intro assump_5
    have assump_21 : ((False ∧ False) → False) := by
      intro assump_9
      cases assump_9
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
    let assump_8 := assump_5 assump_21
    apply False.elim assump_8
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p1 : Prop)
theorem file57_107703 : ((((((False → False) ∨ (p1 → False)) → ((False → False) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((False → False) ∨ (p1 → False)) → ((False → False) → False)) → False) := by
    intro assump_5
    have assump_23 : ((False → False) ∨ (p1 → False)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_23
    have assump_24 : (False → False) := by
      intro assump_13
      apply False.elim assump_13
    let assump_12 := assump_8 assump_24
    apply False.elim assump_12
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p3 p7 p6 p4 p0 : Prop)
theorem file57_108401 : (((((p0 ∨ p0) → False) → ((p0 → False) → (p7 ∧ p3))) ∨ (((p6 → False) → False) → ((p2 ∧ p4) → False))) → ((((p4 → True) ∧ (False ∨ True)) ∧ ((p6 ∧ False) ∧ (p3 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_6
      case inl assump_9 =>
        apply False.elim assump_9
      case inr assump_10 =>
        cases assump_4
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply False.elim assump_18


variable (p1 p5 p4 p3 : Prop)
theorem file57_109066 : (((((p4 ∨ p3) ∨ (True ∨ p5)) ∨ ((p1 → False) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : (((p4 ∨ p3) ∨ (True ∨ p5)) ∨ ((p1 → False) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p5 p4 p7 p3 p2 p6 p1 : Prop)
theorem file57_109438 : (((((p6 ∧ False) → (p2 → p2)) → ((False ∨ False) → (p6 → p7))) ∨ (((p1 → False) ∧ (p7 → p2)) ∧ ((p3 → False) → False))) ∧ ((((True ∨ False) → False) → ((True → True) → (True ∨ p4))) ∨ (((p3 → p7) → False) ∨ ((p5 → False) → False)))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    apply False.elim assump_6
  case inr assump_7 =>
    apply False.elim assump_7
  apply Or.inl
  intro assump_12
  intro assump_13
  apply Or.inl
  apply True.intro


variable (p1 p0 p3 p4 p7 : Prop)
theorem file57_110026 : ((((((False ∨ False) ∨ (p7 → False)) ∨ ((p1 ∨ p0) ∧ (True ∧ p7))) → (((p1 → p4) → False) → ((True ∧ p4) → (p0 → p3)))) → False) → False) := by
  intro assump_1
  have assump_80 : ((((False ∨ False) ∨ (p7 → False)) ∨ ((p1 ∨ p0) ∧ (True ∧ p7))) → (((p1 → p4) → False) → ((True ∧ p4) → (p0 → p3)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_7
    case intro assump_11 assump_12 =>
      cases assump_5
      case inl assump_19 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_21
          case inl assump_23 =>
            apply False.elim assump_23
          case inr assump_24 =>
            apply False.elim assump_24
        case inr assump_22 =>
          have assump_81 : (p1 → p4) := by
            intro assump_33
            exact assump_12
          let assump_32 := assump_6 assump_81
          apply False.elim assump_32
      case inr assump_20 =>
        cases assump_20
        case intro assump_39 assump_40 =>
          cases assump_39
          case inl assump_41 =>
            cases assump_40
            case intro assump_45 assump_46 =>
              have assump_82 : (p1 → p4) := by
                intro assump_54
                exact assump_12
              let assump_53 := assump_6 assump_82
              apply False.elim assump_53
          case inr assump_42 =>
            cases assump_40
            case intro assump_62 assump_63 =>
              have assump_83 : (p1 → p4) := by
                intro assump_71
                exact assump_12
              let assump_70 := assump_6 assump_83
              apply False.elim assump_70
  let assump_4 := assump_1 assump_80
  apply False.elim assump_4


variable (p7 p1 p2 p6 p4 p0 p3 : Prop)
theorem file57_111808 : (((((True ∧ p0) → (p2 → p3)) → False) ∧ (((p4 → False) ∧ (p2 → p7)) ∧ ((p0 → False) ∨ (True → False)))) → ((((p6 → p6) → (True → False)) ∧ ((True ∧ p6) → False)) ∧ (((p0 → True) → False) → ((p1 ∨ False) → False)))) := by
  intro assump_1
  apply And.intro
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_9
    case intro assump_12 assump_13 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        cases assump_13
        case inl assump_20 =>
          have assump_160 : ((True ∧ p0) → (p2 → p3)) := by
            intro assump_28
            intro assump_29
            cases assump_28
            case intro assump_32 assump_33 =>
              have assump_161 : p0 := by
                exact assump_33
              let assump_40 := assump_20 assump_161
              apply False.elim assump_40
          let assump_27 := assump_8 assump_160
          apply False.elim assump_27
        case inr assump_21 =>
          have assump_162 : True := by
            apply True.intro
          let assump_49 := assump_21 assump_162
          apply False.elim assump_49
  intro assump_53
  cases assump_53
  case intro assump_54 assump_55 =>
    cases assump_1
    case intro assump_60 assump_61 =>
      cases assump_61
      case intro assump_64 assump_65 =>
        cases assump_64
        case intro assump_66 assump_67 =>
          cases assump_65
          case inl assump_72 =>
            have assump_163 : ((True ∧ p0) → (p2 → p3)) := by
              intro assump_80
              intro assump_81
              cases assump_80
              case intro assump_84 assump_85 =>
                have assump_164 : p0 := by
                  exact assump_85
                let assump_92 := assump_72 assump_164
                apply False.elim assump_92
            let assump_79 := assump_60 assump_163
            apply False.elim assump_79
          case inr assump_73 =>
            have assump_165 : True := by
              apply True.intro
            let assump_101 := assump_73 assump_165
            apply False.elim assump_101
  intro assump_105
  intro assump_106
  cases assump_106
  case inl assump_107 =>
    cases assump_1
    case intro assump_113 assump_114 =>
      cases assump_114
      case intro assump_117 assump_118 =>
        cases assump_117
        case intro assump_119 assump_120 =>
          cases assump_118
          case inl assump_125 =>
            have assump_166 : ((True ∧ p0) → (p2 → p3)) := by
              intro assump_133
              intro assump_134
              cases assump_133
              case intro assump_137 assump_138 =>
                have assump_167 : p0 := by
                  exact assump_138
                let assump_145 := assump_125 assump_167
                apply False.elim assump_145
            let assump_132 := assump_113 assump_166
            apply False.elim assump_132
          case inr assump_126 =>
            have assump_168 : True := by
              apply True.intro
            let assump_154 := assump_126 assump_168
            apply False.elim assump_154
  case inr assump_108 =>
    apply False.elim assump_108


variable (p2 p1 p4 : Prop)
theorem file57_115051 : ((((((p4 ∧ p1) ∨ (True ∨ False)) ∧ ((p2 ∨ True) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_37 : ((((p4 ∧ p1) ∨ (True ∨ False)) ∧ ((p2 ∨ True) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_38 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_18 := assump_7 assump_38
          apply False.elim assump_18
      case inr assump_9 =>
        cases assump_9
        case inl assump_22 =>
          have assump_39 : (p2 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_28 := assump_7 assump_39
          apply False.elim assump_28
        case inr assump_23 =>
          apply False.elim assump_23
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p4 p7 p3 p5 : Prop)
theorem file57_116066 : ((((((p5 ∨ p3) ∧ (True → p5)) ∧ ((p4 → True) → False)) → (((p3 ∧ True) ∧ (p5 ∧ p7)) → False)) → False) → False) := by
  intro assump_1
  have assump_52 : ((((p5 ∨ p3) ∧ (True → p5)) ∧ ((p4 → True) → False)) → (((p3 ∧ True) ∧ (p5 ∧ p7)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          cases assump_5
          case intro assump_21 assump_22 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_23
              case inl assump_25 =>
                have assump_53 : (p4 → True) := by
                  intro assump_34
                  apply True.intro
                let assump_33 := assump_22 assump_53
                apply False.elim assump_33
              case inr assump_26 =>
                have assump_54 : (p4 → True) := by
                  intro assump_45
                  apply True.intro
                let assump_44 := assump_22 assump_54
                apply False.elim assump_44
  let assump_4 := assump_1 assump_52
  apply False.elim assump_4


variable (p4 p2 p3 p7 p0 p6 p1 p5 : Prop)
theorem file57_117344 : (((((p4 → p7) ∧ (p0 → p1)) → ((p3 ∨ True) → False)) → (((p3 → p2) ∨ (p6 → p5)) → ((p5 → p5) ∨ (p7 ∧ p4)))) ∨ ((((False → p0) → False) → ((True → False) ∧ (p4 → False))) ∨ (((p0 ∨ p4) ∨ (p4 → False)) → ((p6 ∧ p0) ∨ (p4 ∧ p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    exact assump_9
  case inr assump_4 =>
    apply Or.inl
    intro assump_16
    exact assump_16


variable (p5 p4 p3 p0 : Prop)
theorem file57_117856 : ((((((p3 ∨ False) ∨ (p3 → False)) → False) → (((p5 ∧ False) → (p0 → False)) → ((p4 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_29 : ((((p3 ∨ False) ∨ (p3 → False)) → False) → (((p5 ∧ False) → (p0 → False)) → ((p4 → False) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_30 : ((p3 ∨ False) ∨ (p3 → False)) := by
      apply Or.inr
      intro assump_15
      have assump_31 : ((p3 ∨ False) ∨ (p3 → False)) := by
        apply Or.inl
        apply Or.inl
        exact assump_15
      let assump_19 := assump_5 assump_31
      apply False.elim assump_19
    let assump_14 := assump_5 assump_30
    apply False.elim assump_14
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p5 p7 p6 p0 p3 : Prop)
theorem file57_118674 : ((((((False ∧ p3) → False) ∨ ((p7 ∨ p0) ∨ (False ∨ p3))) ∨ (((p0 ∨ False) ∨ (p5 ∧ p6)) ∨ ((p6 → p6) → False))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((False ∧ p3) → False) ∨ ((p7 ∨ p0) ∨ (False ∨ p3))) ∨ (((p0 ∨ False) ∨ (p5 ∧ p6)) ∨ ((p6 → p6) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_6
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p3 p4 p2 p6 p1 p5 : Prop)
theorem file57_119225 : (((((p6 → p6) → (p2 ∧ p4)) → False) ∧ (((True ∨ p5) → False) ∧ ((p3 ∧ p2) ∧ (p6 ∨ p2)))) → ((((p3 ∨ p3) → (p4 → False)) → False) → (((False → p6) ∧ (p1 → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_1
    case intro assump_12 assump_13 =>
      cases assump_13
      case intro assump_16 assump_17 =>
        cases assump_17
        case intro assump_20 assump_21 =>
          cases assump_20
          case intro assump_22 assump_23 =>
            cases assump_21
            case inl assump_28 =>
              have assump_48 : (True ∨ p5) := by
                apply Or.inl
                apply True.intro
              let assump_35 := assump_16 assump_48
              apply False.elim assump_35
            case inr assump_29 =>
              have assump_49 : (True ∨ p5) := by
                apply Or.inl
                apply True.intro
              let assump_44 := assump_16 assump_49
              apply False.elim assump_44


variable (p4 p6 p3 p0 p2 : Prop)
theorem file57_120320 : ((((((True → False) ∧ (p6 ∨ p2)) → False) ∨ (((p0 ∧ p3) ∨ (p4 ∧ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_29 : ((((True → False) ∧ (p6 ∨ p2)) → False) ∨ (((p0 ∧ p3) ∨ (p4 ∧ p0)) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        have assump_30 : True := by
          apply True.intro
        let assump_15 := assump_6 assump_30
        apply False.elim assump_15
      case inr assump_11 =>
        have assump_31 : True := by
          apply True.intro
        let assump_22 := assump_6 assump_31
        apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p0 p4 p7 p6 p3 p2 p5 : Prop)
theorem file57_121122 : ((((((p3 → False) ∨ (p5 ∧ p3)) ∧ ((p3 ∧ p2) ∧ (p4 → p7))) ∧ (((p6 → False) ∨ (p7 → p0)) ∧ ((p0 ∨ True) → False))) ∧ ((((p5 → p3) → False) → False) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_13
          case intro assump_18 assump_19 =>
            cases assump_18
            case intro assump_20 assump_21 =>
              cases assump_11
              case intro assump_28 assump_29 =>
                cases assump_28
                case inl assump_30 =>
                  have assump_132 : (((p5 → p3) → False) → False) := by
                    intro assump_39
                    have assump_133 : (p5 → p3) := by
                      intro assump_43
                      exact assump_20
                    let assump_42 := assump_39 assump_133
                    apply False.elim assump_42
                  let assump_38 := assump_9 assump_132
                  apply False.elim assump_38
                case inr assump_31 =>
                  have assump_134 : (((p5 → p3) → False) → False) := by
                    intro assump_59
                    have assump_135 : (p5 → p3) := by
                      intro assump_63
                      exact assump_20
                    let assump_62 := assump_59 assump_135
                    apply False.elim assump_62
                  let assump_58 := assump_9 assump_134
                  apply False.elim assump_58
        case inr assump_15 =>
          cases assump_15
          case intro assump_72 assump_73 =>
            cases assump_13
            case intro assump_78 assump_79 =>
              cases assump_78
              case intro assump_80 assump_81 =>
                cases assump_11
                case intro assump_88 assump_89 =>
                  cases assump_88
                  case inl assump_90 =>
                    have assump_136 : (((p5 → p3) → False) → False) := by
                      intro assump_99
                      have assump_137 : (p5 → p3) := by
                        intro assump_103
                        exact assump_80
                      let assump_102 := assump_99 assump_137
                      apply False.elim assump_102
                    let assump_98 := assump_9 assump_136
                    apply False.elim assump_98
                  case inr assump_91 =>
                    have assump_138 : (((p5 → p3) → False) → False) := by
                      intro assump_119
                      have assump_139 : (p5 → p3) := by
                        intro assump_123
                        exact assump_80
                      let assump_122 := assump_119 assump_139
                      apply False.elim assump_122
                    let assump_118 := assump_9 assump_138
                    apply False.elim assump_118


variable (p4 p6 p3 p5 p0 p2 : Prop)
theorem file57_124191 : ((((((False → p2) ∧ (p0 → True)) → ((p4 → False) ∧ (False ∨ True))) → False) ∧ ((((p6 ∨ p5) ∨ (p4 ∨ p0)) → False) ∧ (((p4 ∨ True) ∨ (p3 → p2)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_16 : ((p4 ∨ True) ∨ (p3 → p2)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_12 := assump_7 assump_16
      apply False.elim assump_12


variable (p4 p2 p1 p6 : Prop)
theorem file57_124734 : (((((p2 → False) → False) ∨ ((p2 → p2) → False)) ∧ (((p1 ∨ p6) → (p4 ∨ True)) → ((p1 → p1) → (False ∧ p2)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_46 : ((p1 ∨ p6) → (p4 ∨ True)) := by
        intro assump_11
        cases assump_11
        case inl assump_12 =>
          apply Or.inr
          apply True.intro
        case inr assump_13 =>
          apply Or.inr
          apply True.intro
      let assump_10 := assump_3 assump_46
      have assump_47 : (p1 → p1) := by
        intro assump_19
        exact assump_19
      let assump_18 := assump_10 assump_47
      let assump_22 := And.left assump_18
      apply False.elim assump_22
    case inr assump_5 =>
      have assump_48 : ((p1 ∨ p6) → (p4 ∨ True)) := by
        intro assump_31
        cases assump_31
        case inl assump_32 =>
          apply Or.inr
          apply True.intro
        case inr assump_33 =>
          apply Or.inr
          apply True.intro
      let assump_30 := assump_3 assump_48
      have assump_49 : (p1 → p1) := by
        intro assump_39
        exact assump_39
      let assump_38 := assump_30 assump_49
      let assump_42 := And.left assump_38
      apply False.elim assump_42


variable (p7 p1 p4 : Prop)
theorem file57_126066 : (((((p7 → False) ∧ (True → False)) ∧ ((p1 ∨ False) ∧ (p1 ∧ False))) ∧ (((p4 ∨ False) → False) ∧ ((p7 ∧ p4) → False))) → False) := by
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      cases assump_28
      case intro assump_30 assump_31 =>
        cases assump_29
        case intro assump_36 assump_37 =>
          cases assump_36
          case inl assump_38 =>
            cases assump_37
            case intro assump_42 assump_43 =>
              apply False.elim assump_43
          case inr assump_39 =>
            apply False.elim assump_39


variable (p6 p1 p3 p7 p0 : Prop)
theorem file57_126758 : (((((p0 ∨ p3) → (p0 ∨ p0)) ∧ ((p1 → False) → False)) ∧ (((True ∨ p7) → (p1 → False)) ∧ ((False → p6) ∨ (p6 → False)))) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_9
      case intro assump_16 assump_17 =>
        cases assump_17
        case inl assump_20 =>
          have assump_60 : (p1 → False) := by
            intro assump_28
            have assump_61 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_33 := assump_16 assump_61
            have assump_62 : p1 := by
              exact assump_28
            let assump_34 := assump_33 assump_62
            apply False.elim assump_34
          let assump_27 := assump_11 assump_60
          apply False.elim assump_27
        case inr assump_21 =>
          have assump_63 : (p1 → False) := by
            intro assump_47
            have assump_64 : (True ∨ p7) := by
              apply Or.inl
              apply True.intro
            let assump_52 := assump_16 assump_64
            have assump_65 : p1 := by
              exact assump_47
            let assump_53 := assump_52 assump_65
            apply False.elim assump_53
          let assump_46 := assump_11 assump_63
          apply False.elim assump_46


variable (p2 p7 p6 p1 p0 p4 p5 : Prop)
theorem file57_128161 : ((((((p6 → p4) → (p2 ∧ p2)) ∨ ((p5 ∧ p1) ∧ (p0 → p6))) → (((p2 ∨ True) → False) → ((p7 → True) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_28 : ((((p6 → p4) → (p2 ∧ p2)) ∨ ((p5 ∧ p1) ∧ (p0 → p6))) → (((p2 ∨ True) → False) → ((p7 → True) ∨ (p0 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case inl assump_9 =>
      apply Or.inl
      intro assump_13
      apply True.intro
    case inr assump_10 =>
      cases assump_10
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          apply Or.inl
          intro assump_24
          apply True.intro
  let assump_4 := assump_1 assump_28
  apply False.elim assump_4


variable (p2 p1 p7 p3 p6 p4 p0 : Prop)
theorem file57_128955 : (((((p0 ∨ p0) ∧ (p4 → p6)) ∧ ((True → p6) → (p2 ∨ p4))) ∧ (((p1 ∨ p2) → False) ∧ ((p4 ∧ p3) → False))) ∨ ((((True → False) ∧ (p0 → False)) ∨ ((p2 → p7) → False)) → (((p0 → False) → (p7 → False)) ∨ ((p3 → False) → False)))) := by
  apply Or.inr
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      have assump_40 : True := by
        apply True.intro
      let assump_19 := assump_4 assump_40
      apply False.elim assump_19
  case inr assump_3 =>
    apply Or.inl
    intro assump_25
    intro assump_26
    have assump_41 : (p2 → p7) := by
      intro assump_34
      exact assump_26
    let assump_33 := assump_3 assump_41
    apply False.elim assump_33


variable (p7 p1 p3 p4 : Prop)
theorem file57_129794 : (((((True ∧ False) → (True → p1)) ∧ ((p7 → p3) → False)) ∧ (((p7 → True) → False) ∧ ((p4 → p7) ∧ (False ∧ p7)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply False.elim assump_18


variable (p6 p5 p1 p4 p0 p2 p7 p3 : Prop)
theorem file57_130347 : (((((p5 ∧ p6) ∧ (p2 ∧ False)) ∨ ((True ∨ p4) ∧ (p5 → False))) ∨ (((p5 ∨ p3) ∨ (p1 → False)) → ((p5 ∧ True) → (False → p1)))) → ((((p1 ∨ p2) ∨ (p4 → p7)) → ((p6 ∧ p7) → False)) → (((p3 → False) ∧ (p0 ∧ False)) → ((p0 → p3) → False)))) := by
  intro assump_42
  intro assump_43
  intro assump_44
  intro assump_45
  cases assump_44
  case intro assump_48 assump_49 =>
    cases assump_49
    case intro assump_52 assump_53 =>
      apply False.elim assump_53


variable (p1 p4 p2 p0 p6 p3 p7 : Prop)
theorem file57_130867 : (((((p0 → p6) → False) → False) ∨ (((p6 → False) ∨ (p1 → p7)) ∧ ((p7 ∧ True) ∧ (p4 → False)))) → ((((p4 ∧ True) → False) → False) → (((p2 ∨ p3) ∨ (p4 ∨ True)) ∨ ((p3 → p0) ∨ (p3 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    apply Or.inl
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_10
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            apply Or.inl
            apply Or.inr
            apply Or.inr
            apply True.intro
      case inr assump_12 =>
        cases assump_10
        case intro assump_27 assump_28 =>
          cases assump_27
          case intro assump_29 assump_30 =>
            apply Or.inl
            apply Or.inr
            apply Or.inr
            apply True.intro


variable (p5 p6 p0 p1 p3 p7 p4 p2 : Prop)
theorem file57_131909 : (((((p4 ∧ True) ∧ (p2 ∧ p2)) → False) → (((p0 ∨ p1) → (p5 → False)) ∨ ((False → False) ∧ (p4 ∨ p2)))) → ((((p5 ∨ False) → (p7 ∧ p6)) ∨ ((p3 → False) ∨ (p6 → False))) → (((p3 → p3) ∨ (p4 ∧ p6)) ∧ ((p0 ∨ True) ∨ (p0 ∧ p3))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    exact assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_12 =>
      apply Or.inl
      intro assump_18
      exact assump_18
    case inr assump_13 =>
      apply Or.inl
      intro assump_25
      exact assump_25
  cases assump_2
  case inl assump_28 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_29 =>
    cases assump_29
    case inl assump_34 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_35 =>
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p3 p0 p5 p4 p6 p7 p1 : Prop)
theorem file57_132883 : (((((p4 → False) ∧ (False ∨ False)) ∧ ((p1 ∨ False) → (p6 ∨ p7))) → (((False ∧ False) ∨ (p3 → p1)) → False)) ∨ ((((p5 → p6) ∨ (p3 ∨ p1)) ∧ ((p7 ∨ True) ∨ (p6 ∧ p4))) → (((p3 → False) → False) → ((False ∨ False) ∨ (p0 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  case inr assump_4 =>
    cases assump_1
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          apply False.elim assump_17
        case inr assump_18 =>
          apply False.elim assump_18


variable (p5 p6 p3 p1 : Prop)
theorem file57_133649 : (((((p1 ∨ False) → (p3 ∨ True)) ∨ ((p5 ∨ True) → (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_15 : (((p1 ∨ False) → (p3 ∨ True)) ∨ ((p5 ∨ True) → (p6 → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p6 p2 p4 p5 : Prop)
theorem file57_134142 : (((((p4 → p2) → False) ∧ ((p2 ∨ p7) → (p6 ∧ p7))) ∨ (((p4 ∧ p4) ∧ (p4 → p4)) ∨ ((p4 → True) → (p2 ∧ p2)))) → ((((p5 ∨ p5) → (p7 ∧ False)) → False) → (((True → False) → False) → ((p7 ∨ p7) → (False → True))))) := by
  intro assump_23
  intro assump_24
  intro assump_25
  intro assump_26
  intro assump_27
  apply True.intro


variable (p3 p1 p4 p6 p2 p7 p0 : Prop)
theorem file57_134529 : (((((p2 ∨ p2) → (p6 ∧ p7)) ∨ ((p4 ∨ p1) ∨ (True ∨ p0))) ∨ (((p7 ∧ p4) ∧ (p7 ∨ p3)) → ((p2 ∧ p3) ∨ (p7 ∨ p4)))) → ((((p6 → p6) → False) ∨ ((p3 → True) ∧ (True → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        have assump_133 : (p6 → p6) := by
          intro assump_15
          exact assump_15
        let assump_14 := assump_3 assump_133
        apply False.elim assump_14
      case inr assump_10 =>
        cases assump_10
        case inl assump_21 =>
          cases assump_21
          case inl assump_23 =>
            have assump_134 : (p6 → p6) := by
              intro assump_29
              exact assump_29
            let assump_28 := assump_3 assump_134
            apply False.elim assump_28
          case inr assump_24 =>
            have assump_135 : (p6 → p6) := by
              intro assump_39
              exact assump_39
            let assump_38 := assump_3 assump_135
            apply False.elim assump_38
        case inr assump_22 =>
          cases assump_22
          case inl assump_45 =>
            have assump_136 : (p6 → p6) := by
              intro assump_50
              exact assump_50
            let assump_49 := assump_3 assump_136
            apply False.elim assump_49
          case inr assump_46 =>
            have assump_137 : (p6 → p6) := by
              intro assump_60
              exact assump_60
            let assump_59 := assump_3 assump_137
            apply False.elim assump_59
    case inr assump_8 =>
      have assump_138 : (p6 → p6) := by
        intro assump_70
        exact assump_70
      let assump_69 := assump_3 assump_138
      apply False.elim assump_69
  case inr assump_4 =>
    cases assump_4
    case intro assump_76 assump_77 =>
      cases assump_1
      case inl assump_82 =>
        cases assump_82
        case inl assump_84 =>
          have assump_139 : True := by
            apply True.intro
          let assump_89 := assump_77 assump_139
          apply False.elim assump_89
        case inr assump_85 =>
          cases assump_85
          case inl assump_93 =>
            cases assump_93
            case inl assump_95 =>
              have assump_140 : True := by
                apply True.intro
              let assump_100 := assump_77 assump_140
              apply False.elim assump_100
            case inr assump_96 =>
              have assump_141 : True := by
                apply True.intro
              let assump_107 := assump_77 assump_141
              apply False.elim assump_107
          case inr assump_94 =>
            cases assump_94
            case inl assump_111 =>
              have assump_142 : True := by
                apply True.intro
              let assump_115 := assump_77 assump_142
              apply False.elim assump_115
            case inr assump_112 =>
              have assump_143 : True := by
                apply True.intro
              let assump_122 := assump_77 assump_143
              apply False.elim assump_122
      case inr assump_83 =>
        have assump_144 : True := by
          apply True.intro
        let assump_129 := assump_77 assump_144
        apply False.elim assump_129


variable (p0 p6 p5 p3 p2 : Prop)
theorem file57_137877 : ((((((p6 → False) → False) → False) → False) ∧ ((((p5 → False) → (True ∧ True)) ∨ ((p6 ∨ p0) ∨ (p3 → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p5 → False) → (True ∧ True)) ∨ ((p6 ∨ p0) ∨ (p3 → p2))) := by
      apply Or.inl
      intro assump_9
      apply And.intro
      apply True.intro
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p3 p6 p4 p1 p0 p5 : Prop)
theorem file57_138400 : ((((((p3 ∧ p0) ∧ (p3 ∨ p4)) ∧ ((p3 ∨ p0) → False)) ∧ (((p3 ∨ p1) ∨ (p6 ∨ p5)) ∧ ((True ∨ True) → False))) ∨ ((((False → p1) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
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
              cases assump_5
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case inl assump_26 =>
                    have assump_122 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_32 := assump_23 assump_122
                    apply False.elim assump_32
                  case inr assump_27 =>
                    have assump_123 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_40 := assump_23 assump_123
                    apply False.elim assump_40
                case inr assump_25 =>
                  cases assump_25
                  case inl assump_44 =>
                    have assump_124 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_50 := assump_23 assump_124
                    apply False.elim assump_50
                  case inr assump_45 =>
                    have assump_125 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_58 := assump_23 assump_125
                    apply False.elim assump_58
            case inr assump_17 =>
              cases assump_5
              case intro assump_66 assump_67 =>
                cases assump_66
                case inl assump_68 =>
                  cases assump_68
                  case inl assump_70 =>
                    have assump_126 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_76 := assump_67 assump_126
                    apply False.elim assump_76
                  case inr assump_71 =>
                    have assump_127 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_84 := assump_67 assump_127
                    apply False.elim assump_84
                case inr assump_69 =>
                  cases assump_69
                  case inl assump_88 =>
                    have assump_128 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_94 := assump_67 assump_128
                    apply False.elim assump_94
                  case inr assump_89 =>
                    have assump_129 : (True ∨ True) := by
                      apply Or.inl
                      apply True.intro
                    let assump_102 := assump_67 assump_129
                    apply False.elim assump_102
  case inr assump_3 =>
    have assump_130 : (((False → p1) → False) → False) := by
      intro assump_109
      have assump_131 : (False → p1) := by
        intro assump_113
        apply False.elim assump_113
      let assump_112 := assump_109 assump_131
      apply False.elim assump_112
    let assump_108 := assump_3 assump_130
    apply False.elim assump_108


