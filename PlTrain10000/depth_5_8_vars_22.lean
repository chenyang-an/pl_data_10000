variable (p6 p0 p5 p2 p7 p3 : Prop)
theorem file22_44 : (((((p0 ∧ p5) → (True → p0)) ∨ ((p3 ∨ p5) ∨ (False → False))) → False) → ((((p3 ∧ p6) → (p7 ∨ p6)) → False) ∨ (((p7 → True) → False) ∧ ((p6 → p6) → (p2 → p6))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_22 : (((p0 ∧ p5) → (True → p0)) ∨ ((p3 ∨ p5) ∨ (False → False))) := by
    apply Or.inl
    intro assump_9
    intro assump_10
    cases assump_9
    case intro assump_13 assump_14 =>
      exact assump_13
  let assump_8 := assump_1 assump_22
  apply False.elim assump_8


variable (p2 p4 p3 p0 p7 : Prop)
theorem file22_603 : ((((((p3 → False) ∨ (p0 ∧ p2)) → ((True → False) ∨ (p2 ∧ p4))) → False) ∧ ((((True ∨ p4) → False) → ((p2 ∨ p7) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_32 : (((True ∨ p4) → False) → ((p2 ∨ p7) → False)) := by
      intro assump_9
      intro assump_10
      cases assump_10
      case inl assump_11 =>
        have assump_33 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_17 := assump_9 assump_33
        apply False.elim assump_17
      case inr assump_12 =>
        have assump_34 : (True ∨ p4) := by
          apply Or.inl
          apply True.intro
        let assump_25 := assump_9 assump_34
        apply False.elim assump_25
    let assump_8 := assump_3 assump_32
    apply False.elim assump_8


variable (p5 p4 p1 p2 p0 p7 : Prop)
theorem file22_1484 : (((((p4 ∧ False) ∧ (True → p4)) → ((True ∨ p7) → (False → False))) ∨ (((p2 → False) → False) → False)) → ((((p5 ∨ p0) ∧ (p5 ∧ False)) → ((p1 → False) ∨ (p1 → False))) ∨ (((p1 ∨ p4) ∧ (p0 ∧ p1)) → ((p1 ∧ p4) → (True → False))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_8
        case intro assump_13 assump_14 =>
          apply False.elim assump_14
      case inr assump_10 =>
        cases assump_8
        case intro assump_21 assump_22 =>
          apply False.elim assump_22
  case inr assump_3 =>
    apply Or.inl
    intro assump_29
    cases assump_29
    case intro assump_30 assump_31 =>
      cases assump_30
      case inl assump_32 =>
        cases assump_31
        case intro assump_36 assump_37 =>
          apply False.elim assump_37
      case inr assump_33 =>
        cases assump_31
        case intro assump_44 assump_45 =>
          apply False.elim assump_45


variable (p4 p2 p5 p7 p6 p3 p0 p1 : Prop)
theorem file22_2614 : ((((((p6 ∧ p2) → False) → ((p5 → p3) ∧ (p5 ∧ p4))) ∨ (((p3 ∧ p3) ∧ (p7 ∧ p0)) → False)) ∧ ((((p3 → False) ∧ (p1 ∧ p7)) → False) ∧ (((True → False) ∧ (p2 ∨ p4)) ∧ ((p3 → False) ∧ (p1 ∨ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            cases assump_15
            case inl assump_18 =>
              cases assump_13
              case intro assump_22 assump_23 =>
                cases assump_23
                case inl assump_26 =>
                  have assump_138 : True := by
                    apply True.intro
                  let assump_33 := assump_14 assump_138
                  apply False.elim assump_33
                case inr assump_27 =>
                  have assump_139 : True := by
                    apply True.intro
                  let assump_42 := assump_14 assump_139
                  apply False.elim assump_42
            case inr assump_19 =>
              cases assump_13
              case intro assump_48 assump_49 =>
                cases assump_49
                case inl assump_52 =>
                  have assump_140 : True := by
                    apply True.intro
                  let assump_59 := assump_14 assump_140
                  apply False.elim assump_59
                case inr assump_53 =>
                  have assump_141 : True := by
                    apply True.intro
                  let assump_68 := assump_14 assump_141
                  apply False.elim assump_68
    case inr assump_5 =>
      cases assump_3
      case intro assump_74 assump_75 =>
        cases assump_75
        case intro assump_78 assump_79 =>
          cases assump_78
          case intro assump_80 assump_81 =>
            cases assump_81
            case inl assump_84 =>
              cases assump_79
              case intro assump_88 assump_89 =>
                cases assump_89
                case inl assump_92 =>
                  have assump_142 : True := by
                    apply True.intro
                  let assump_99 := assump_80 assump_142
                  apply False.elim assump_99
                case inr assump_93 =>
                  have assump_143 : True := by
                    apply True.intro
                  let assump_108 := assump_80 assump_143
                  apply False.elim assump_108
            case inr assump_85 =>
              cases assump_79
              case intro assump_114 assump_115 =>
                cases assump_115
                case inl assump_118 =>
                  have assump_144 : True := by
                    apply True.intro
                  let assump_125 := assump_80 assump_144
                  apply False.elim assump_125
                case inr assump_119 =>
                  have assump_145 : True := by
                    apply True.intro
                  let assump_134 := assump_80 assump_145
                  apply False.elim assump_134


variable (p1 p5 p0 p3 p6 : Prop)
theorem file22_5833 : (((((p3 ∨ p1) ∧ (p1 ∧ p0)) → False) → False) → ((((p0 → False) ∧ (True ∧ True)) → False) ∨ (((p0 → True) ∨ (p6 ∨ p5)) ∧ ((p0 → p0) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      have assump_55 : (((p3 ∨ p1) ∧ (p1 ∧ p0)) → False) := by
        intro assump_17
        cases assump_17
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            cases assump_19
            case intro assump_24 assump_25 =>
              have assump_56 : p0 := by
                exact assump_25
              let assump_33 := assump_5 assump_56
              apply False.elim assump_33
          case inr assump_21 =>
            cases assump_19
            case intro assump_39 assump_40 =>
              have assump_57 : p0 := by
                exact assump_40
              let assump_48 := assump_5 assump_57
              apply False.elim assump_48
      let assump_16 := assump_1 assump_55
      apply False.elim assump_16


variable (p4 p0 p3 p2 p7 p1 p6 : Prop)
theorem file22_6993 : (((((p7 ∨ p1) ∨ (p1 ∨ p3)) → False) ∧ (((p0 → False) ∨ (p2 → p6)) ∧ ((True ∧ p4) ∧ (p0 ∧ False)))) → False) := by
  intro assump_41
  cases assump_41
  case intro assump_42 assump_43 =>
    cases assump_43
    case intro assump_46 assump_47 =>
      cases assump_46
      case inl assump_48 =>
        cases assump_47
        case intro assump_52 assump_53 =>
          cases assump_52
          case intro assump_54 assump_55 =>
            cases assump_53
            case intro assump_60 assump_61 =>
              apply False.elim assump_61
      case inr assump_49 =>
        cases assump_47
        case intro assump_68 assump_69 =>
          cases assump_68
          case intro assump_70 assump_71 =>
            cases assump_69
            case intro assump_76 assump_77 =>
              apply False.elim assump_77


variable (p0 p5 p2 p1 p3 p7 p4 p6 : Prop)
theorem file22_7883 : (((((p2 → False) ∧ (p1 → False)) ∧ ((False → False) ∨ (True ∧ p0))) → (((p6 ∨ p1) → (p0 → p2)) ∧ ((False → False) → (p2 ∨ p2)))) → ((((p3 → False) → (False → False)) ∨ ((p4 ∧ False) → False)) ∨ (((p7 → False) ∨ (p5 ∨ p0)) ∨ ((p3 ∧ p4) ∨ (True → p6))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  apply False.elim assump_5


variable (p0 p5 p7 p1 p4 p6 : Prop)
theorem file22_8311 : (((((False ∨ p7) → False) ∧ ((True ∨ p1) → False)) ∧ (((p5 → p7) ∨ (p6 ∧ p0)) ∨ ((True ∧ p5) → False))) → ((((p1 ∧ p1) → False) → False) → (((p4 → p4) → False) ∧ ((p4 → False) ∧ (p7 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    cases assump_8
    case intro assump_10 assump_11 =>
      cases assump_9
      case inl assump_16 =>
        cases assump_16
        case inl assump_18 =>
          have assump_132 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_23 := assump_11 assump_132
          apply False.elim assump_23
        case inr assump_19 =>
          cases assump_19
          case intro assump_27 assump_28 =>
            have assump_133 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_35 := assump_11 assump_133
            apply False.elim assump_35
      case inr assump_17 =>
        have assump_134 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_42 := assump_11 assump_134
        apply False.elim assump_42
  apply And.intro
  intro assump_46
  cases assump_1
  case intro assump_51 assump_52 =>
    cases assump_51
    case intro assump_53 assump_54 =>
      cases assump_52
      case inl assump_59 =>
        cases assump_59
        case inl assump_61 =>
          have assump_135 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_66 := assump_54 assump_135
          apply False.elim assump_66
        case inr assump_62 =>
          cases assump_62
          case intro assump_70 assump_71 =>
            have assump_136 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_78 := assump_54 assump_136
            apply False.elim assump_78
      case inr assump_60 =>
        have assump_137 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_85 := assump_54 assump_137
        apply False.elim assump_85
  intro assump_89
  cases assump_1
  case intro assump_94 assump_95 =>
    cases assump_94
    case intro assump_96 assump_97 =>
      cases assump_95
      case inl assump_102 =>
        cases assump_102
        case inl assump_104 =>
          have assump_138 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_109 := assump_97 assump_138
          apply False.elim assump_109
        case inr assump_105 =>
          cases assump_105
          case intro assump_113 assump_114 =>
            have assump_139 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_121 := assump_97 assump_139
            apply False.elim assump_121
      case inr assump_103 =>
        have assump_140 : (True ∨ p1) := by
          apply Or.inl
          apply True.intro
        let assump_128 := assump_97 assump_140
        apply False.elim assump_128


variable (p7 p3 p2 p0 p5 p6 p4 : Prop)
theorem file22_11402 : (((((False → p6) ∨ (p0 ∧ p2)) ∨ ((p5 ∨ p7) → False)) ∨ (((p5 → False) ∧ (p3 → False)) → ((False ∧ False) → (p3 ∨ p6)))) ∨ ((((p4 ∧ p3) → (p6 → False)) → ((p5 → p5) → False)) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_14
  apply False.elim assump_14


variable (p4 p6 p1 p5 p2 p7 : Prop)
theorem file22_11759 : ((((((True ∧ False) → False) → False) ∧ (((p1 → p7) ∨ (p6 ∧ p6)) → False)) ∧ ((((p2 ∨ True) ∨ (p5 ∧ p4)) ∨ ((p7 ∧ p7) ∨ (True → False))) → False)) → False) := by
  intro assump_20
  cases assump_20
  case intro assump_21 assump_22 =>
    cases assump_21
    case intro assump_23 assump_24 =>
      have assump_35 : (((p2 ∨ True) ∨ (p5 ∧ p4)) ∨ ((p7 ∧ p7) ∨ (True → False))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_31 := assump_22 assump_35
      apply False.elim assump_31


variable (p4 p2 : Prop)
theorem file22_12351 : ((((((True → False) → (p2 → p4)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) → (p2 → p4)) → False) → False) := by
    intro assump_5
    have assump_26 : ((True → False) → (p2 → p4)) := by
      intro assump_9
      intro assump_10
      have assump_27 : True := by
        apply True.intro
      let assump_15 := assump_9 assump_27
      apply False.elim assump_15
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p2 p7 p1 p4 p5 p0 p6 : Prop)
theorem file22_12966 : (((((p0 → p2) → False) ∧ ((p1 ∧ p2) ∧ (False ∧ False))) ∧ (((p7 → p1) ∨ (True → p1)) → False)) → ((((p2 → p4) ∨ (p1 → False)) ∨ ((p6 ∧ p4) ∨ (True → p5))) → False)) := by
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
          case intro assump_15 assump_16 =>
            cases assump_15
            case intro assump_17 assump_18 =>
              cases assump_16
              case intro assump_23 assump_24 =>
                apply False.elim assump_23
    case inr assump_6 =>
      cases assump_1
      case intro assump_29 assump_30 =>
        cases assump_29
        case intro assump_31 assump_32 =>
          cases assump_32
          case intro assump_35 assump_36 =>
            cases assump_35
            case intro assump_37 assump_38 =>
              cases assump_36
              case intro assump_43 assump_44 =>
                apply False.elim assump_43
  case inr assump_4 =>
    cases assump_4
    case inl assump_47 =>
      cases assump_47
      case intro assump_49 assump_50 =>
        cases assump_1
        case intro assump_55 assump_56 =>
          cases assump_55
          case intro assump_57 assump_58 =>
            cases assump_58
            case intro assump_61 assump_62 =>
              cases assump_61
              case intro assump_63 assump_64 =>
                cases assump_62
                case intro assump_69 assump_70 =>
                  apply False.elim assump_69
    case inr assump_48 =>
      cases assump_1
      case intro assump_75 assump_76 =>
        cases assump_75
        case intro assump_77 assump_78 =>
          cases assump_78
          case intro assump_81 assump_82 =>
            cases assump_81
            case intro assump_83 assump_84 =>
              cases assump_82
              case intro assump_89 assump_90 =>
                apply False.elim assump_89


variable (p5 p3 p1 p0 p4 p2 p6 p7 : Prop)
theorem file22_15090 : ((((((True ∧ p7) → (p2 ∨ False)) → ((p5 → p7) ∧ (p7 ∨ p3))) ∧ (((True → False) ∧ (p4 ∨ p1)) ∨ ((p7 → p2) → (p7 → False)))) ∧ ((((p5 → False) ∧ (False ∧ p2)) → ((p3 → p6) ∨ (p4 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            have assump_67 : (((p5 → False) ∧ (False ∧ p2)) → ((p3 → p6) ∨ (p4 ∧ p0))) := by
              intro assump_21
              cases assump_21
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26
            let assump_20 := assump_3 assump_67
            apply False.elim assump_20
          case inr assump_15 =>
            have assump_68 : (((p5 → False) ∧ (False ∧ p2)) → ((p3 → p6) ∨ (p4 ∧ p0))) := by
              intro assump_38
              cases assump_38
              case intro assump_39 assump_40 =>
                cases assump_40
                case intro assump_43 assump_44 =>
                  apply False.elim assump_43
            let assump_37 := assump_3 assump_68
            apply False.elim assump_37
      case inr assump_9 =>
        have assump_69 : (((p5 → False) ∧ (False ∧ p2)) → ((p3 → p6) ∨ (p4 ∧ p0))) := by
          intro assump_55
          cases assump_55
          case intro assump_56 assump_57 =>
            cases assump_57
            case intro assump_60 assump_61 =>
              apply False.elim assump_60
        let assump_54 := assump_3 assump_69
        apply False.elim assump_54


variable (p6 p2 p5 p1 p3 p0 p7 p4 : Prop)
theorem file22_16927 : (((((p2 → p1) ∧ (True → False)) → False) ∧ (((True → False) ∨ (p6 ∧ False)) → False)) ∨ ((((p4 ∨ p5) ∨ (p1 → False)) ∨ ((True ∧ p7) → (False → p1))) → (((p1 ∧ p4) → False) ∧ ((p3 → p5) ∧ (p3 ∨ p0))))) := by
  apply Or.inl
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_27 : True := by
      apply True.intro
    let assump_8 := assump_3 assump_27
    apply False.elim assump_8
  intro assump_12
  cases assump_12
  case inl assump_13 =>
    have assump_28 : True := by
      apply True.intro
    let assump_17 := assump_13 assump_28
    apply False.elim assump_17
  case inr assump_14 =>
    cases assump_14
    case intro assump_21 assump_22 =>
      apply False.elim assump_22


variable (p6 p7 p3 p1 p4 : Prop)
theorem file22_17718 : (((((p7 ∧ p4) ∧ (False ∧ p3)) → ((p6 → p1) ∧ (p6 → p7))) → False) → False) := by
  intro assump_1
  have assump_39 : (((p7 ∧ p4) ∧ (False ∧ p3)) → ((p6 → p1) ∧ (p6 → p7))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
    intro assump_21
    cases assump_5
    case intro assump_24 assump_25 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_25
        case intro assump_32 assump_33 =>
          apply False.elim assump_32
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p0 p2 p6 p4 p3 p5 : Prop)
theorem file22_18541 : (((((p4 ∨ True) ∧ (p0 → False)) → ((p4 ∧ False) → False)) → (((True → False) → False) → False)) → ((((p2 ∧ p5) → (False ∧ p6)) ∨ ((False → False) → (p0 → False))) ∨ (((p2 ∧ p5) ∧ (p3 → False)) ∧ ((False → False) → (p4 → False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply And.intro
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_61 : (((p4 ∨ True) ∧ (p0 → False)) → ((p4 ∧ False) → False)) := by
      intro assump_14
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    let assump_13 := assump_1 assump_61
    have assump_62 : ((True → False) → False) := by
      intro assump_23
      have assump_63 : True := by
        apply True.intro
      let assump_26 := assump_23 assump_63
      apply False.elim assump_26
    let assump_22 := assump_13 assump_62
    apply False.elim assump_22
  cases assump_4
  case intro assump_33 assump_34 =>
    have assump_64 : (((p4 ∨ True) ∧ (p0 → False)) → ((p4 ∧ False) → False)) := by
      intro assump_42
      intro assump_43
      cases assump_43
      case intro assump_44 assump_45 =>
        apply False.elim assump_45
    let assump_41 := assump_1 assump_64
    have assump_65 : ((True → False) → False) := by
      intro assump_51
      have assump_66 : True := by
        apply True.intro
      let assump_54 := assump_51 assump_66
      apply False.elim assump_54
    let assump_50 := assump_41 assump_65
    apply False.elim assump_50


variable (p3 p5 p7 p6 p4 : Prop)
theorem file22_20111 : ((((((False ∧ False) → False) → False) → (((p7 ∨ False) ∨ (True ∨ p5)) ∧ ((p3 → False) ∨ (False ∧ p6)))) ∧ ((((False ∧ p5) ∧ (p4 → p3)) → False) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_25 : (((False ∧ p5) ∧ (p4 → p3)) → False) := by
      intro assump_15
      cases assump_15
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
    let assump_14 := assump_9 assump_25
    apply False.elim assump_14


variable (p6 p4 p0 p7 p2 p1 p5 : Prop)
theorem file22_20734 : (((((False → False) ∧ (p2 ∨ p7)) ∨ ((p5 ∨ p2) → (False ∨ True))) → (((p5 → p0) ∧ (False ∨ True)) → ((p1 → False) ∧ (p6 → False)))) → ((((False → False) ∧ (p5 ∧ p5)) → ((p4 ∧ p2) → (False → p4))) ∨ (((p7 → p4) → False) → ((p5 → p4) ∨ (p4 ∧ p1))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  apply False.elim assump_6


variable (p4 p7 p5 p6 p2 : Prop)
theorem file22_21155 : ((((((p6 ∨ True) → False) → False) ∧ (((p5 ∨ p7) → False) → ((p4 ∨ p2) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_38 : ((((p6 ∨ True) → False) → False) ∧ (((p5 ∨ p7) → False) → ((p4 ∨ p2) → (p5 → False)))) := by
    apply And.intro
    intro assump_5
    have assump_39 : (p6 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_8 := assump_5 assump_39
    apply False.elim assump_8
    intro assump_12
    intro assump_13
    intro assump_14
    cases assump_13
    case inl assump_17 =>
      have assump_40 : (p5 ∨ p7) := by
        apply Or.inl
        exact assump_14
      let assump_23 := assump_12 assump_40
      apply False.elim assump_23
    case inr assump_18 =>
      have assump_41 : (p5 ∨ p7) := by
        apply Or.inl
        exact assump_14
      let assump_31 := assump_12 assump_41
      apply False.elim assump_31
  let assump_4 := assump_1 assump_38
  apply False.elim assump_4


variable (p2 p5 p6 p1 p0 p7 : Prop)
theorem file22_22163 : ((((((p5 → False) ∧ (p2 → False)) ∧ ((p7 ∨ p6) ∧ (p6 ∧ p1))) → (((p0 ∨ p7) → False) → ((p6 → True) → (False → p2)))) → False) → False) := by
  intro assump_21
  have assump_34 : ((((p5 → False) ∧ (p2 → False)) ∧ ((p7 ∨ p6) ∧ (p6 ∧ p1))) → (((p0 ∨ p7) → False) → ((p6 → True) → (False → p2)))) := by
    intro assump_25
    intro assump_26
    intro assump_27
    intro assump_28
    apply False.elim assump_28
  let assump_24 := assump_21 assump_34
  apply False.elim assump_24


variable (p7 p3 p1 p6 p4 p0 p5 : Prop)
theorem file22_22704 : (((((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) → False) → ((((p0 ∨ p6) ∧ (p7 ∨ p1)) → ((p7 → p4) ∧ (p3 ∧ p3))) ∧ (((True → False) → False) ∨ ((p1 ∧ p7) → (p7 ∨ p0))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case inl assump_12 =>
        have assump_303 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_19
          cases assump_19
          case inl assump_20 =>
            apply Or.inl
            intro assump_24
            exact assump_24
          case inr assump_21 =>
            apply Or.inl
            intro assump_29
            exact assump_29
        let assump_18 := assump_1 assump_303
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_304 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_40
          cases assump_40
          case inl assump_41 =>
            apply Or.inl
            intro assump_45
            exact assump_45
          case inr assump_42 =>
            apply Or.inl
            intro assump_50
            exact assump_50
        let assump_39 := assump_1 assump_304
        apply False.elim assump_39
    case inr assump_9 =>
      cases assump_7
      case inl assump_58 =>
        have assump_305 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_65
          cases assump_65
          case inl assump_66 =>
            apply Or.inl
            intro assump_70
            exact assump_70
          case inr assump_67 =>
            apply Or.inl
            intro assump_75
            exact assump_75
        let assump_64 := assump_1 assump_305
        apply False.elim assump_64
      case inr assump_59 =>
        have assump_306 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_86
          cases assump_86
          case inl assump_87 =>
            apply Or.inl
            intro assump_91
            exact assump_91
          case inr assump_88 =>
            apply Or.inl
            intro assump_96
            exact assump_96
        let assump_85 := assump_1 assump_306
        apply False.elim assump_85
  apply And.intro
  cases assump_2
  case intro assump_102 assump_103 =>
    cases assump_102
    case inl assump_104 =>
      cases assump_103
      case inl assump_108 =>
        have assump_307 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_115
          cases assump_115
          case inl assump_116 =>
            apply Or.inl
            intro assump_120
            exact assump_120
          case inr assump_117 =>
            apply Or.inl
            intro assump_125
            exact assump_125
        let assump_114 := assump_1 assump_307
        apply False.elim assump_114
      case inr assump_109 =>
        have assump_308 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_136
          cases assump_136
          case inl assump_137 =>
            apply Or.inl
            intro assump_141
            exact assump_141
          case inr assump_138 =>
            apply Or.inl
            intro assump_146
            exact assump_146
        let assump_135 := assump_1 assump_308
        apply False.elim assump_135
    case inr assump_105 =>
      cases assump_103
      case inl assump_154 =>
        have assump_309 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_161
          cases assump_161
          case inl assump_162 =>
            apply Or.inl
            intro assump_166
            exact assump_166
          case inr assump_163 =>
            apply Or.inl
            intro assump_171
            exact assump_171
        let assump_160 := assump_1 assump_309
        apply False.elim assump_160
      case inr assump_155 =>
        have assump_310 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_182
          cases assump_182
          case inl assump_183 =>
            apply Or.inl
            intro assump_187
            exact assump_187
          case inr assump_184 =>
            apply Or.inl
            intro assump_192
            exact assump_192
        let assump_181 := assump_1 assump_310
        apply False.elim assump_181
  cases assump_2
  case intro assump_198 assump_199 =>
    cases assump_198
    case inl assump_200 =>
      cases assump_199
      case inl assump_204 =>
        have assump_311 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_211
          cases assump_211
          case inl assump_212 =>
            apply Or.inl
            intro assump_216
            exact assump_216
          case inr assump_213 =>
            apply Or.inl
            intro assump_221
            exact assump_221
        let assump_210 := assump_1 assump_311
        apply False.elim assump_210
      case inr assump_205 =>
        have assump_312 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_232
          cases assump_232
          case inl assump_233 =>
            apply Or.inl
            intro assump_237
            exact assump_237
          case inr assump_234 =>
            apply Or.inl
            intro assump_242
            exact assump_242
        let assump_231 := assump_1 assump_312
        apply False.elim assump_231
    case inr assump_201 =>
      cases assump_199
      case inl assump_250 =>
        have assump_313 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_257
          cases assump_257
          case inl assump_258 =>
            apply Or.inl
            intro assump_262
            exact assump_262
          case inr assump_259 =>
            apply Or.inl
            intro assump_267
            exact assump_267
        let assump_256 := assump_1 assump_313
        apply False.elim assump_256
      case inr assump_251 =>
        have assump_314 : (((p6 → False) ∨ (p3 → True)) → ((p3 → p3) ∨ (p3 ∨ p5))) := by
          intro assump_278
          cases assump_278
          case inl assump_279 =>
            apply Or.inl
            intro assump_283
            exact assump_283
          case inr assump_280 =>
            apply Or.inl
            intro assump_288
            exact assump_288
        let assump_277 := assump_1 assump_314
        apply False.elim assump_277
  apply Or.inl
  intro assump_296
  have assump_315 : True := by
    apply True.intro
  let assump_299 := assump_296 assump_315
  apply False.elim assump_299


variable (p3 p7 : Prop)
theorem file22_29503 : (((((True → False) ∧ (p3 ∨ p7)) → False) → False) → False) := by
  intro assump_1
  have assump_29 : (((True → False) ∧ (p3 ∨ p7)) → False) := by
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


variable (p4 p1 p0 p7 p6 p2 p5 : Prop)
theorem file22_30212 : (((((p6 → True) → False) ∨ ((p7 ∨ p5) ∧ (p0 ∨ p4))) → (((False ∧ p0) → False) → ((p4 ∨ False) → False))) → ((((False ∧ True) ∨ (p5 → False)) → ((True → False) → (p2 → False))) ∨ (((p4 → p5) → (False → False)) ∨ ((p6 → False) ∨ (p5 → p1))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  intro assump_5
  intro assump_6
  cases assump_4
  case inl assump_11 =>
    cases assump_11
    case intro assump_13 assump_14 =>
      apply False.elim assump_13
  case inr assump_12 =>
    have assump_24 : True := by
      apply True.intro
    let assump_20 := assump_5 assump_24
    apply False.elim assump_20


variable (p7 p1 p0 p4 p5 : Prop)
theorem file22_30881 : (((((p7 ∧ False) ∧ (p1 → False)) → False) → False) → ((((p4 ∨ p0) → (p5 → False)) → ((p7 ∧ p0) → False)) → False)) := by
  intro assump_1
  intro assump_2
  have assump_20 : (((p7 ∧ False) ∧ (p1 → False)) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_7 := assump_1 assump_20
  apply False.elim assump_7


variable (p7 p3 p0 p1 p6 p2 p4 p5 : Prop)
theorem file22_31403 : ((((((p6 → p3) → (p1 → False)) ∨ ((p0 → p5) ∨ (True ∧ True))) → (((p4 → False) ∧ (p5 → True)) ∧ ((p5 ∧ p3) → (p7 ∨ p6)))) ∧ ((((p2 → True) ∨ (p1 ∨ p6)) ∨ ((p2 ∧ p2) ∨ (p2 ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : (((p2 → True) ∨ (p1 ∨ p6)) ∨ ((p2 ∧ p2) ∨ (p2 ∧ False))) := by
      apply Or.inl
      apply Or.inl
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p3 p0 p4 p5 p7 : Prop)
theorem file22_31970 : (((((False → False) ∨ (p3 → False)) → False) → (((p5 → p7) → (True ∨ p7)) ∧ ((p3 ∧ False) → (p3 ∧ p5)))) → ((((p7 → p0) ∨ (p3 → False)) → ((p3 ∧ p5) → False)) → (((p7 ∨ p4) ∨ (p4 → False)) → ((p5 → p5) ∨ (p5 ∨ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      apply Or.inl
      intro assump_14
      exact assump_14
    case inr assump_7 =>
      apply Or.inl
      intro assump_23
      exact assump_23
  case inr assump_5 =>
    apply Or.inl
    intro assump_32
    exact assump_32


variable (p4 p0 p7 p1 p3 p6 p2 p5 : Prop)
theorem file22_32626 : (((((p5 → p7) ∧ (p2 ∧ p1)) ∨ ((p1 ∨ p0) → (p2 → False))) → (((p4 ∨ p7) → False) → ((p4 ∨ p6) ∧ (False ∨ p3)))) → ((((p5 → p3) ∧ (p6 → p6)) ∧ ((False ∧ p6) ∧ (True ∧ p7))) → (((False ∨ p4) ∨ (p5 → False)) → False))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_7
  case inl assump_8 =>
    cases assump_8
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      cases assump_6
      case intro assump_16 assump_17 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_17
          case intro assump_24 assump_25 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              apply False.elim assump_26
  case inr assump_9 =>
    cases assump_6
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_33
        case intro assump_40 assump_41 =>
          cases assump_40
          case intro assump_42 assump_43 =>
            apply False.elim assump_42


variable (p2 p5 p0 p1 p7 p6 p4 : Prop)
theorem file22_33734 : (((((p0 ∨ p2) → False) → False) → False) → ((((p6 → False) → False) ∧ ((True → p6) → (p5 → p1))) → (((p7 → False) → False) → ((p0 ∧ p4) → (p1 → p5))))) := by
  intro assump_46
  intro assump_47
  intro assump_48
  intro assump_49
  intro assump_50
  cases assump_49
  case intro assump_53 assump_54 =>
    cases assump_47
    case intro assump_61 assump_62 =>
      have assump_80 : (((p0 ∨ p2) → False) → False) := by
        intro assump_70
        have assump_81 : (p0 ∨ p2) := by
          apply Or.inl
          exact assump_53
        let assump_73 := assump_70 assump_81
        apply False.elim assump_73
      let assump_69 := assump_46 assump_80
      apply False.elim assump_69


variable (p2 p5 p6 p1 p7 p3 p0 : Prop)
theorem file22_34486 : (((((p7 → False) ∨ (p0 ∨ p1)) → False) → (((p0 ∧ True) ∨ (True → p7)) → ((False ∧ p6) → False))) ∧ ((((p0 ∧ p3) → False) ∧ ((p6 ∧ p7) → (p5 ∨ p1))) → (((p2 → False) → (False → True)) ∨ ((p6 → p0) ∧ (p2 → p5))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_4
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    apply Or.inl
    intro assump_15
    intro assump_16
    apply True.intro


variable (p0 p6 p7 p5 p3 p2 p1 : Prop)
theorem file22_35064 : (((((p6 ∨ p3) → (p6 ∨ p1)) → ((p5 ∧ p5) ∧ (p1 → p3))) → (((False ∧ p1) ∨ (p0 ∧ False)) → False)) ∨ ((((p1 ∧ p2) ∧ (p2 ∨ p7)) ∨ ((p7 → False) ∧ (p6 ∨ p0))) ∨ (((p1 → False) ∨ (p1 ∧ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  case inr assump_4 =>
    cases assump_4
    case intro assump_9 assump_10 =>
      apply False.elim assump_10


variable (p2 p0 p6 p1 p5 : Prop)
theorem file22_35611 : (((((p6 → p1) ∧ (p0 → False)) → ((p5 → p2) → (True → True))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p6 → p1) ∧ (p0 → False)) → ((p5 → p2) → (True → True))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p5 p6 p3 p2 p4 p1 : Prop)
theorem file22_36003 : (((((p2 → p1) → False) ∧ ((p0 → False) → False)) ∧ (((p2 ∨ p4) → False) → ((p5 → False) ∧ (False → p6)))) → ((((p3 → False) ∨ (p1 ∧ p6)) ∧ ((p3 ∨ p6) ∧ (p0 ∧ False))) → (((p6 → p3) ∨ (True ∧ p3)) ∨ ((p2 → False) ∨ (False ∨ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_4
      case intro assump_9 assump_10 =>
        cases assump_9
        case inl assump_11 =>
          cases assump_10
          case intro assump_15 assump_16 =>
            apply False.elim assump_16
        case inr assump_12 =>
          cases assump_10
          case intro assump_23 assump_24 =>
            apply False.elim assump_24
    case inr assump_6 =>
      cases assump_6
      case intro assump_29 assump_30 =>
        cases assump_4
        case intro assump_35 assump_36 =>
          cases assump_35
          case inl assump_37 =>
            cases assump_36
            case intro assump_41 assump_42 =>
              apply False.elim assump_42
          case inr assump_38 =>
            cases assump_36
            case intro assump_49 assump_50 =>
              apply False.elim assump_50


variable (p6 p2 p4 p1 p0 p7 p5 p3 : Prop)
theorem file22_37267 : (((((False ∧ p6) ∧ (True → False)) → False) ∨ (((p0 ∧ p1) → False) ∧ ((p1 → p5) ∧ (p7 ∧ False)))) ∨ ((((False ∧ p2) ∧ (p5 ∧ p3)) → ((p6 ∨ p0) → False)) → (((p4 → False) → (p6 → False)) ∧ ((p4 ∨ p0) ∧ (True ∧ True))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply False.elim assump_4


variable (p0 p3 : Prop)
theorem file22_37724 : ((((((p0 ∨ p3) ∨ (p3 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p0 ∨ p3) ∨ (p3 → False)) → False) → False) := by
    intro assump_5
    have assump_24 : ((p0 ∨ p3) ∨ (p3 → False)) := by
      apply Or.inr
      intro assump_9
      have assump_25 : ((p0 ∨ p3) ∨ (p3 → False)) := by
        apply Or.inl
        apply Or.inr
        exact assump_9
      let assump_13 := assump_5 assump_25
      apply False.elim assump_13
    let assump_8 := assump_5 assump_24
    apply False.elim assump_8
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p7 p1 p2 p6 p0 : Prop)
theorem file22_38389 : ((((((p2 ∨ p1) ∨ (p2 ∨ p0)) ∨ ((p0 ∧ p0) → (p6 ∨ False))) ∨ (((False → p7) ∧ (False ∨ False)) ∨ ((True ∧ p7) → (p5 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p2 ∨ p1) ∨ (p2 ∨ p0)) ∨ ((p0 ∧ p0) → (p6 ∨ False))) ∨ (((False → p7) ∧ (False ∨ False)) ∨ ((True ∧ p7) → (p5 ∧ False)))) := by
    apply Or.inl
    apply Or.inr
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_22 : ((((p2 ∨ p1) ∨ (p2 ∨ p0)) ∨ ((p0 ∧ p0) → (p6 ∨ False))) ∨ (((False → p7) ∧ (False ∨ False)) ∨ ((True ∧ p7) → (p5 ∧ False)))) := by
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply Or.inr
        exact assump_7
      let assump_14 := assump_1 assump_22
      apply False.elim assump_14
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p2 p7 p0 p3 p6 p5 : Prop)
theorem file22_39276 : ((((((p2 ∧ p6) ∧ (False ∧ p6)) ∧ ((p3 → p5) ∨ (p3 → p7))) → (((p3 ∧ False) → (p6 → False)) ∨ ((False ∧ p3) ∧ (p3 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p2 ∧ p6) ∧ (False ∧ p6)) ∧ ((p3 → p5) ∨ (p3 → p7))) → (((p3 ∧ False) → (p6 → False)) ∨ ((False ∧ p3) ∧ (p3 ∨ p0)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p2 p7 p1 p3 p6 : Prop)
theorem file22_40012 : (((((p3 → p7) → (p6 → False)) → False) → (((p6 ∧ False) ∧ (True → p2)) → False)) ∨ ((((p2 → False) ∧ (p1 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_6


variable (p3 p1 p2 p0 : Prop)
theorem file22_40393 : (((((False → p3) ∨ (p1 → p2)) → False) → (((p1 → False) → False) ∨ ((p0 ∧ p2) → (False ∧ p0)))) ∧ ((((p0 ∧ p0) ∧ (p3 ∧ False)) ∨ ((False → False) ∨ (p1 ∨ p1))) → (((p0 → False) ∧ (True → False)) → False))) := by
  apply And.intro
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_64 : ((False → p3) ∨ (p1 → p2)) := by
    apply Or.inl
    intro assump_9
    apply False.elim assump_9
  let assump_8 := assump_1 assump_64
  apply False.elim assump_8
  intro assump_15
  intro assump_16
  cases assump_16
  case intro assump_17 assump_18 =>
    cases assump_15
    case inl assump_23 =>
      cases assump_23
      case intro assump_25 assump_26 =>
        cases assump_25
        case intro assump_27 assump_28 =>
          cases assump_26
          case intro assump_33 assump_34 =>
            apply False.elim assump_34
    case inr assump_24 =>
      cases assump_24
      case inl assump_39 =>
        have assump_65 : True := by
          apply True.intro
        let assump_44 := assump_18 assump_65
        apply False.elim assump_44
      case inr assump_40 =>
        cases assump_40
        case inl assump_48 =>
          have assump_66 : True := by
            apply True.intro
          let assump_53 := assump_18 assump_66
          apply False.elim assump_53
        case inr assump_49 =>
          have assump_67 : True := by
            apply True.intro
          let assump_60 := assump_18 assump_67
          apply False.elim assump_60


variable (p5 p1 p3 p6 p2 p7 p0 p4 : Prop)
theorem file22_41927 : (((((p1 ∧ p4) ∨ (p6 → True)) ∧ ((True ∧ p5) → (False → False))) → (((False → False) → False) ∧ ((p5 ∧ p6) → (p7 ∧ p4)))) → ((((p2 ∨ p0) ∧ (False ∨ p7)) → False) → (((True ∧ p7) ∧ (p5 ∨ p0)) ∧ ((p1 → p5) ∨ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  apply And.intro
  apply And.intro
  apply And.intro
  apply True.intro
  have assump_61 : (((p1 ∧ p4) ∨ (p6 → True)) ∧ ((True ∧ p5) → (False → False))) := by
    apply And.intro
    apply Or.inr
    intro assump_8
    apply True.intro
    intro assump_9
    intro assump_10
    apply False.elim assump_10
  let assump_7 := assump_1 assump_61
  let assump_13 := And.left assump_7
  have assump_62 : (False → False) := by
    intro assump_15
    apply False.elim assump_15
  let assump_14 := assump_13 assump_62
  apply False.elim assump_14
  have assump_63 : (((p1 ∧ p4) ∨ (p6 → True)) ∧ ((True ∧ p5) → (False → False))) := by
    apply And.intro
    apply Or.inr
    intro assump_26
    apply True.intro
    intro assump_27
    intro assump_28
    apply False.elim assump_28
  let assump_25 := assump_1 assump_63
  let assump_31 := And.left assump_25
  have assump_64 : (False → False) := by
    intro assump_33
    apply False.elim assump_33
  let assump_32 := assump_31 assump_64
  apply False.elim assump_32
  apply Or.inl
  intro assump_43
  have assump_65 : (((p1 ∧ p4) ∨ (p6 → True)) ∧ ((True ∧ p5) → (False → False))) := by
    apply And.intro
    apply Or.inr
    intro assump_48
    apply True.intro
    intro assump_49
    intro assump_50
    apply False.elim assump_50
  let assump_47 := assump_1 assump_65
  let assump_53 := And.left assump_47
  have assump_66 : (False → False) := by
    intro assump_55
    apply False.elim assump_55
  let assump_54 := assump_53 assump_66
  apply False.elim assump_54


variable (p7 p5 p4 p3 p2 : Prop)
theorem file22_43764 : ((((((p3 → False) ∧ (p4 ∨ p5)) ∧ ((p2 ∨ p3) ∧ (p7 ∧ p4))) → (((p2 ∧ p7) ∧ (p4 ∨ p2)) → ((p2 ∧ p5) ∨ (p7 → p4)))) → False) → False) := by
  intro assump_1
  have assump_140 : ((((p3 → False) ∧ (p4 ∨ p5)) ∧ ((p2 ∨ p3) ∧ (p7 ∧ p4))) → (((p2 ∧ p7) ∧ (p4 ∨ p2)) → ((p2 ∧ p5) ∨ (p7 → p4)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          cases assump_5
          case intro assump_19 assump_20 =>
            cases assump_19
            case intro assump_21 assump_22 =>
              cases assump_22
              case inl assump_25 =>
                cases assump_20
                case intro assump_29 assump_30 =>
                  cases assump_29
                  case inl assump_31 =>
                    cases assump_30
                    case intro assump_35 assump_36 =>
                      apply Or.inr
                      intro assump_41
                      exact assump_36
                  case inr assump_32 =>
                    cases assump_30
                    case intro assump_46 assump_47 =>
                      apply Or.inr
                      intro assump_52
                      exact assump_47
              case inr assump_26 =>
                cases assump_20
                case intro assump_57 assump_58 =>
                  cases assump_57
                  case inl assump_59 =>
                    cases assump_58
                    case intro assump_63 assump_64 =>
                      apply Or.inl
                      apply And.intro
                      exact assump_59
                      exact assump_26
                  case inr assump_60 =>
                    cases assump_58
                    case intro assump_71 assump_72 =>
                      apply Or.inl
                      apply And.intro
                      exact assump_9
                      exact assump_26
        case inr assump_16 =>
          cases assump_5
          case intro assump_79 assump_80 =>
            cases assump_79
            case intro assump_81 assump_82 =>
              cases assump_82
              case inl assump_85 =>
                cases assump_80
                case intro assump_89 assump_90 =>
                  cases assump_89
                  case inl assump_91 =>
                    cases assump_90
                    case intro assump_95 assump_96 =>
                      apply Or.inr
                      intro assump_101
                      exact assump_96
                  case inr assump_92 =>
                    cases assump_90
                    case intro assump_106 assump_107 =>
                      apply Or.inr
                      intro assump_112
                      exact assump_107
              case inr assump_86 =>
                cases assump_80
                case intro assump_117 assump_118 =>
                  cases assump_117
                  case inl assump_119 =>
                    cases assump_118
                    case intro assump_123 assump_124 =>
                      apply Or.inl
                      apply And.intro
                      exact assump_119
                      exact assump_86
                  case inr assump_120 =>
                    cases assump_118
                    case intro assump_131 assump_132 =>
                      apply Or.inl
                      apply And.intro
                      exact assump_16
                      exact assump_86
  let assump_4 := assump_1 assump_140
  apply False.elim assump_4


variable (p7 p5 p4 p2 p6 p3 p1 : Prop)
theorem file22_47470 : (((((p4 ∨ True) ∨ (p1 ∧ p6)) → ((p3 → False) → False)) → False) → ((((p2 ∨ p3) ∨ (p1 ∨ p4)) ∨ ((False ∨ False) → (p2 → False))) ∨ (((p7 ∧ True) ∧ (p5 ∨ p5)) ∧ ((p1 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  intro assump_4
  intro assump_5
  cases assump_4
  case inl assump_8 =>
    apply False.elim assump_8
  case inr assump_9 =>
    apply False.elim assump_9


variable (p3 p7 p4 p0 p1 : Prop)
theorem file22_47922 : ((((((p7 ∧ p3) ∧ (True ∨ True)) → ((p0 → False) → (p7 ∨ p4))) ∨ (((p1 → p1) → (False ∨ p3)) ∧ ((p4 ∨ False) ∨ (True → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p7 ∧ p3) ∧ (True ∨ True)) → ((p0 → False) → (p7 ∨ p4))) ∨ (((p1 → p1) → (False ∨ p3)) ∧ ((p4 ∨ False) ∨ (True → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_10
        case inl assump_17 =>
          apply Or.inl
          exact assump_11
        case inr assump_18 =>
          apply Or.inl
          exact assump_11
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p2 p1 p6 p7 p4 p0 : Prop)
theorem file22_48724 : (((((p0 ∨ p6) → (p7 → False)) ∧ ((p2 → False) → (p1 ∧ p6))) ∨ (((p1 ∧ p5) ∨ (True ∧ True)) → ((p5 → p6) → False))) → ((((p1 → False) ∧ (p5 → p4)) → False) → (((p2 → False) ∨ (p5 → False)) → ((False ∧ True) → (p0 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    apply False.elim assump_8


variable (p0 p5 p7 : Prop)
theorem file22_49172 : (((((False ∧ False) → (p0 → p7)) ∨ ((p7 → p5) ∧ (p5 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ False) → (p0 → p7)) ∨ ((p7 → p5) ∧ (p5 → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p4 p2 p3 p1 p6 p5 : Prop)
theorem file22_49630 : (((((True → p1) ∧ (p5 ∨ p3)) → ((True → p4) ∨ (p6 ∨ p5))) ∧ (((True → False) ∧ (False → p5)) ∧ ((p6 ∧ p2) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_22 : True := by
          apply True.intro
        let assump_18 := assump_8 assump_22
        apply False.elim assump_18


variable (p5 p6 p7 p0 : Prop)
theorem file22_50140 : (((((p6 ∧ p5) ∨ (p6 ∨ True)) ∧ ((p7 ∨ p0) → False)) ∧ (((False → False) → (p7 → False)) ∧ ((False → p7) → False))) → False) := by
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    cases assump_10
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_11
          case intro assump_24 assump_25 =>
            have assump_73 : (False → p7) := by
              intro assump_31
              apply False.elim assump_31
            let assump_30 := assump_25 assump_73
            apply False.elim assump_30
      case inr assump_15 =>
        cases assump_15
        case inl assump_37 =>
          cases assump_11
          case intro assump_43 assump_44 =>
            have assump_74 : (False → p7) := by
              intro assump_50
              apply False.elim assump_50
            let assump_49 := assump_44 assump_74
            apply False.elim assump_49
        case inr assump_38 =>
          cases assump_11
          case intro assump_60 assump_61 =>
            have assump_75 : (False → p7) := by
              intro assump_67
              apply False.elim assump_67
            let assump_66 := assump_61 assump_75
            apply False.elim assump_66


variable (p7 p3 p1 p2 : Prop)
theorem file22_51511 : (((((p7 → False) → False) → ((p2 → p2) ∨ (p1 ∧ p3))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p7 → False) → False) → ((p2 → p2) ∨ (p1 ∧ p3))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p2 p0 p5 p7 p3 p1 p6 : Prop)
theorem file22_51883 : (((((p2 ∧ False) ∧ (p3 → p5)) → ((p7 → False) → False)) → False) → ((((p6 → False) ∨ (p7 ∨ False)) ∧ ((p5 ∨ p1) → (True ∧ p0))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      have assump_55 : (((p2 ∧ False) ∧ (p3 → p5)) → ((p7 → False) → False)) := by
        intro assump_14
        intro assump_15
        cases assump_14
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            apply False.elim assump_21
      let assump_13 := assump_1 assump_55
      apply False.elim assump_13
    case inr assump_6 =>
      cases assump_6
      case inl assump_29 =>
        have assump_56 : (((p2 ∧ False) ∧ (p3 → p5)) → ((p7 → False) → False)) := by
          intro assump_38
          intro assump_39
          cases assump_38
          case intro assump_42 assump_43 =>
            cases assump_42
            case intro assump_44 assump_45 =>
              apply False.elim assump_45
        let assump_37 := assump_1 assump_56
        apply False.elim assump_37
      case inr assump_30 =>
        apply False.elim assump_30


variable (p1 p2 p0 p7 p6 p3 p4 : Prop)
theorem file22_53138 : (((((p3 ∨ True) → False) ∧ ((p1 ∧ True) ∧ (p2 ∨ p1))) → (((p4 ∧ p3) → (False ∧ p1)) ∨ ((p3 → False) → False))) ∨ ((((p1 → p7) → (True ∨ p0)) ∨ ((p6 ∨ p4) ∧ (True → p3))) → (((p7 ∧ p2) → (True → False)) → ((p0 → True) → (p7 → p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case inl assump_14 =>
          apply Or.inl
          intro assump_18
          apply And.intro
          cases assump_18
          case intro assump_19 assump_20 =>
            have assump_62 : (p3 ∨ True) := by
              apply Or.inl
              exact assump_20
            let assump_29 := assump_2 assump_62
            apply False.elim assump_29
          cases assump_18
          case intro assump_33 assump_34 =>
            exact assump_8
        case inr assump_15 =>
          apply Or.inl
          intro assump_41
          apply And.intro
          cases assump_41
          case intro assump_42 assump_43 =>
            have assump_63 : (p3 ∨ True) := by
              apply Or.inl
              exact assump_43
            let assump_52 := assump_2 assump_63
            apply False.elim assump_52
          cases assump_41
          case intro assump_56 assump_57 =>
            exact assump_15


variable (p5 p2 p7 p4 : Prop)
theorem file22_54578 : ((((((True ∨ p4) ∨ (p2 ∨ p7)) ∧ ((False ∧ False) ∧ (p5 ∨ p7))) → False) → False) → False) := by
  intro assump_1
  have assump_49 : ((((True ∨ p4) ∨ (p2 ∨ p7)) ∧ ((False ∧ False) ∧ (p5 ∨ p7))) → False) := by
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
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
        case inr assump_11 =>
          cases assump_7
          case intro assump_22 assump_23 =>
            cases assump_22
            case intro assump_24 assump_25 =>
              apply False.elim assump_24
      case inr assump_9 =>
        cases assump_9
        case inl assump_28 =>
          cases assump_7
          case intro assump_32 assump_33 =>
            cases assump_32
            case intro assump_34 assump_35 =>
              apply False.elim assump_34
        case inr assump_29 =>
          cases assump_7
          case intro assump_40 assump_41 =>
            cases assump_40
            case intro assump_42 assump_43 =>
              apply False.elim assump_42
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p4 p3 p6 p0 p5 : Prop)
theorem file22_55959 : (((((p0 → p5) → (False → False)) ∨ ((p6 → p3) ∨ (p3 → False))) ∧ (((True → False) ∧ (True ∨ p4)) → False)) ∨ ((((True ∨ False) ∨ (p4 → False)) ∧ ((p5 → p3) → (p5 → False))) → False)) := by
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  apply False.elim assump_2
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_7
    case inl assump_10 =>
      have assump_25 : True := by
        apply True.intro
      let assump_14 := assump_6 assump_25
      apply False.elim assump_14
    case inr assump_11 =>
      have assump_26 : True := by
        apply True.intro
      let assump_21 := assump_6 assump_26
      apply False.elim assump_21


variable (p5 p7 p1 p6 p2 p0 p4 : Prop)
theorem file22_56728 : (((((False ∨ p4) ∧ (p4 → p0)) → False) → (((p6 ∨ p2) → (p6 ∧ p5)) ∨ ((p7 → p1) → (p4 ∧ False)))) → ((((True ∨ p0) → (True → False)) → False) ∨ (((p0 ∧ p2) → (p0 ∧ p2)) → False))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_12 : (True ∨ p0) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_4 assump_12
  have assump_13 : True := by
    apply True.intro
  let assump_8 := assump_7 assump_13
  apply False.elim assump_8


variable (p4 p7 p3 p6 p2 p1 p0 : Prop)
theorem file22_57253 : (((((p1 ∨ p2) ∨ (True ∨ False)) ∨ ((p4 ∨ p6) ∨ (p3 ∧ p0))) → (((p7 → True) ∨ (p3 ∧ p7)) → False)) → False) := by
  intro assump_1
  have assump_10 : (((p1 ∨ p2) ∨ (True ∨ False)) ∨ ((p4 ∨ p6) ∨ (p3 ∧ p0))) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_10
  have assump_11 : ((p7 → True) ∨ (p3 ∧ p7)) := by
    apply Or.inl
    intro assump_6
    apply True.intro
  let assump_5 := assump_4 assump_11
  apply False.elim assump_5


variable (p7 p4 p5 p1 p0 p6 : Prop)
theorem file22_57807 : ((((((p4 → p1) ∧ (p5 ∧ p6)) ∧ ((p7 ∧ p0) ∧ (p6 → False))) → False) → False) → False) := by
  intro assump_1
  have assump_35 : ((((p4 → p1) ∧ (p5 ∧ p6)) ∧ ((p7 ∧ p0) ∧ (p6 → False))) → False) := by
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
              have assump_36 : p6 := by
                exact assump_13
              let assump_28 := assump_19 assump_36
              apply False.elim assump_28
  let assump_4 := assump_1 assump_35
  apply False.elim assump_4


variable (p0 : Prop)
theorem file22_58620 : (((((p0 → True) → False) → False) → False) → False) := by
  intro assump_1
  have assump_16 : (((p0 → True) → False) → False) := by
    intro assump_5
    have assump_17 : (p0 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_17
    apply False.elim assump_8
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p6 p2 p4 p0 p7 p3 p5 p1 : Prop)
theorem file22_59054 : ((((((p1 ∨ p2) → (p7 → False)) ∨ ((False ∨ p2) → False)) → (((p7 → True) → (p6 → p7)) ∨ ((p0 → False) → False))) ∧ ((((False ∧ p0) → (True ∨ p3)) ∨ ((p6 → p3) ∧ (p5 ∨ p4))) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    have assump_28 : (((False ∧ p0) → (True ∨ p3)) ∨ ((p6 → p3) ∧ (p5 ∨ p4))) := by
      apply Or.inl
      intro assump_20
      cases assump_20
      case intro assump_21 assump_22 =>
        apply False.elim assump_21
    let assump_19 := assump_14 assump_28
    apply False.elim assump_19


variable (p7 p5 p1 p4 p3 p6 : Prop)
theorem file22_59678 : (((((p7 → False) → (p7 → p4)) → False) → (((p3 → False) ∧ (p5 → False)) → ((p7 → False) ∨ (p3 ∨ False)))) ∨ ((((True ∨ p1) ∧ (False → False)) → False) → (((p1 ∧ p5) ∨ (p6 ∧ False)) ∧ ((p3 → False) ∨ (p1 ∨ p7))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    have assump_29 : ((p7 → False) → (p7 → p4)) := by
      intro assump_16
      intro assump_17
      have assump_30 : p7 := by
        exact assump_17
      let assump_22 := assump_16 assump_30
      apply False.elim assump_22
    let assump_15 := assump_1 assump_29
    apply False.elim assump_15


variable (p3 p4 p7 p1 p5 p2 p0 p6 : Prop)
theorem file22_60401 : (((((p6 → p3) ∧ (p7 ∧ False)) → False) ∨ (((p6 → False) ∨ (p2 → p1)) → ((p5 → False) ∨ (p6 → p1)))) ∨ ((((p5 → True) → (p7 ∧ p1)) → ((p6 ∧ p2) → (p0 → False))) → (((p2 → p0) → (p4 ∧ p2)) ∧ ((p7 → p6) ∨ (p5 → p1))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p6 p1 p2 p5 p0 p3 p7 : Prop)
theorem file22_60871 : (((((False → False) → (p5 ∨ p2)) → ((p0 ∧ False) → (p3 → False))) ∨ (((p1 ∧ p5) ∧ (p0 ∧ False)) → ((False ∨ True) → (p2 → False)))) ∨ ((((p0 ∨ p6) ∧ (p2 ∨ p6)) → False) ∧ (((p0 → p2) → (p7 ∧ False)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    apply False.elim assump_7


variable (p1 p6 p2 p7 p5 : Prop)
theorem file22_61306 : (((((p7 ∧ p5) ∨ (False → False)) ∨ ((True ∨ p6) ∧ (p2 ∨ p1))) → False) → ((((p2 → False) ∧ (p6 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_14 : (((p7 ∧ p5) ∨ (False → False)) ∨ ((True ∨ p6) ∧ (p2 ∨ p1))) := by
    apply Or.inl
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_1 assump_14
  apply False.elim assump_7


variable (p4 p0 p3 p5 p2 p1 : Prop)
theorem file22_61763 : (((((p5 → p5) → (p0 → False)) → ((True ∨ True) ∨ (p1 → p2))) → False) → ((((p5 ∨ p3) → (False → False)) → False) → (((p1 → p3) ∨ (p4 ∨ p1)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    have assump_47 : (((p5 → p5) → (p0 → False)) → ((True ∨ True) ∨ (p1 → p2))) := by
      intro assump_13
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_12 := assump_1 assump_47
    apply False.elim assump_12
  case inr assump_5 =>
    cases assump_5
    case inl assump_19 =>
      have assump_48 : (((p5 → p5) → (p0 → False)) → ((True ∨ True) ∨ (p1 → p2))) := by
        intro assump_28
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_27 := assump_1 assump_48
      apply False.elim assump_27
    case inr assump_20 =>
      have assump_49 : (((p5 → p5) → (p0 → False)) → ((True ∨ True) ∨ (p1 → p2))) := by
        intro assump_41
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_40 := assump_1 assump_49
      apply False.elim assump_40


variable (p6 p0 p7 p3 p5 p4 p1 p2 : Prop)
theorem file22_62919 : ((((((p5 → False) → (p6 → p4)) ∧ ((p1 → False) ∧ (True ∨ p3))) ∧ (((p5 ∨ p4) ∧ (p2 ∧ p0)) → ((True ∨ p7) → (p6 ∧ p7)))) ∧ ((((p6 → False) → False) → False) ∧ (((p1 ∨ True) ∨ (p6 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_11
          case inl assump_14 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              have assump_44 : ((p1 ∨ True) ∨ (p6 → False)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_26 := assump_21 assump_44
              apply False.elim assump_26
          case inr assump_15 =>
            cases assump_3
            case intro assump_34 assump_35 =>
              have assump_45 : ((p1 ∨ True) ∨ (p6 → False)) := by
                apply Or.inl
                apply Or.inr
                apply True.intro
              let assump_40 := assump_35 assump_45
              apply False.elim assump_40


variable (p6 p7 p5 p4 : Prop)
theorem file22_64168 : (((((p6 ∧ p5) ∧ (p7 ∨ True)) ∨ ((p6 ∧ p7) ∨ (False → p4))) → False) → False) := by
  intro assump_1
  have assump_11 : (((p6 ∧ p5) ∧ (p7 ∨ True)) ∨ ((p6 ∧ p7) ∨ (False → p4))) := by
    apply Or.inr
    apply Or.inr
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p6 p5 p0 p1 p4 p3 : Prop)
theorem file22_64561 : (((((True ∨ p3) ∧ (p4 ∧ p1)) → ((p0 → p5) → (True ∧ p3))) ∧ (((True → False) → (p0 ∨ p1)) → False)) → ((((p0 ∨ p7) → False) ∨ ((p6 ∧ p6) → (True → False))) ∧ (((p5 → p1) ∧ (p0 ∧ p4)) ∨ ((p0 → False) → (p1 → False))))) := by
  intro assump_7
  apply And.intro
  cases assump_7
  case intro assump_8 assump_9 =>
    apply Or.inl
    intro assump_14
    cases assump_14
    case inl assump_15 =>
      have assump_77 : ((True → False) → (p0 ∨ p1)) := by
        intro assump_21
        apply Or.inl
        exact assump_15
      let assump_20 := assump_9 assump_77
      apply False.elim assump_20
    case inr assump_16 =>
      have assump_78 : ((True → False) → (p0 ∨ p1)) := by
        intro assump_31
        have assump_79 : True := by
          apply True.intro
        let assump_34 := assump_31 assump_79
        apply False.elim assump_34
      let assump_30 := assump_9 assump_78
      apply False.elim assump_30
  cases assump_7
  case intro assump_41 assump_42 =>
    apply Or.inr
    intro assump_62
    intro assump_63
    have assump_80 : ((True → False) → (p0 ∨ p1)) := by
      intro assump_71
      apply Or.inr
      exact assump_63
    let assump_70 := assump_42 assump_80
    apply False.elim assump_70


variable (p6 p0 p4 p3 p1 p2 p7 : Prop)
theorem file22_65846 : (((((p7 ∨ p2) → False) ∧ ((True ∧ p2) ∧ (p6 → p4))) → False) ∨ ((((p0 ∨ p2) → False) → ((p6 → False) ∨ (p6 ∧ p3))) → (((p3 ∨ p4) ∨ (p0 ∧ p0)) → ((p6 ∧ p7) → (p1 ∨ p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_22 : (p7 ∨ p2) := by
          apply Or.inr
          exact assump_9
        let assump_18 := assump_2 assump_22
        apply False.elim assump_18


variable (p6 p4 p2 p3 p7 : Prop)
theorem file22_66445 : ((((((False ∧ p6) → (False ∧ True)) ∧ ((p2 → False) → (p3 ∧ p2))) → False) ∧ ((((p7 → False) → (False → False)) ∨ ((False → p4) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : (((p7 → False) → (False → False)) ∨ ((False → p4) → False)) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p3 p2 p1 p5 p6 p0 p7 : Prop)
theorem file22_66990 : (((((p0 ∨ p7) ∧ (p6 → p3)) ∧ ((p7 → p5) ∨ (True ∧ p7))) ∨ (((p5 ∨ p3) → (p2 → p2)) ∨ ((p3 → True) → False))) ∨ ((((True ∧ p6) → (p1 → False)) → ((p3 ∧ p2) ∧ (p3 ∧ p3))) ∨ (((True ∧ p7) → (p2 ∨ True)) → ((False ∨ p3) ∧ (p7 ∨ p7))))) := by
  apply Or.inl
  apply Or.inr
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    exact assump_2
  case inr assump_6 =>
    exact assump_2


variable (p2 p6 p4 p5 p3 p0 p1 p7 : Prop)
theorem file22_67474 : (((((p4 ∨ p6) ∧ (p3 ∧ p5)) ∧ ((p5 ∨ p7) ∧ (p1 ∨ True))) → False) → ((((p6 ∧ p1) ∨ (p7 ∨ p1)) ∨ ((False ∨ p1) ∧ (True ∨ True))) ∨ (((p0 ∧ True) → (p4 ∨ p0)) ∨ ((p5 → True) → (p2 ∧ p4))))) := by
  intro assump_1
  apply Or.inr
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    apply Or.inr
    exact assump_5


variable (p7 p0 p1 p5 p4 p2 p6 : Prop)
theorem file22_67881 : ((((((False ∧ True) → False) ∧ ((p6 ∧ p6) → (False → False))) → (((p4 → False) ∧ (p1 → False)) → ((p0 → False) ∧ (p5 → False)))) ∧ ((((False ∧ p4) → (p0 → False)) ∨ ((p5 ∧ p7) ∨ (p7 ∧ p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_20 : (((False ∧ p4) → (p0 → False)) ∨ ((p5 ∧ p7) ∨ (p7 ∧ p2))) := by
      apply Or.inl
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_8 := assump_3 assump_20
    apply False.elim assump_8


variable (p3 p7 p5 p2 p0 p4 : Prop)
theorem file22_68536 : (((((p4 ∧ p3) ∧ (True ∧ p7)) ∨ ((True ∨ p4) ∨ (False ∨ p4))) ∨ (((p3 ∨ p5) ∧ (p5 ∧ p5)) → False)) ∨ ((((p0 ∧ False) ∧ (p0 ∨ p0)) ∨ ((p4 ∨ p2) → False)) ∨ (((p4 → p3) ∧ (p0 ∨ p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p5 p3 p0 p1 p7 p2 : Prop)
theorem file22_68886 : (((((p7 ∧ p1) → False) → ((False → False) → (p2 ∨ p3))) → False) → ((((p0 → False) → False) ∧ ((p7 → p3) ∧ (False ∧ p2))) → (((p5 → False) → (True → False)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_7
    case intro assump_10 assump_11 =>
      cases assump_11
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p6 p0 p1 p3 p5 p2 p4 : Prop)
theorem file22_69379 : (((((p2 ∧ p4) → (p0 → True)) ∨ ((True → False) → False)) ∨ (((p6 ∨ p3) → (p2 → p1)) → ((p0 → False) → False))) ∧ ((((p4 → p4) ∨ (p5 → False)) → False) → False)) := by
  apply And.intro
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  apply True.intro
  intro assump_3
  have assump_13 : ((p4 → p4) ∨ (p5 → False)) := by
    apply Or.inl
    intro assump_7
    exact assump_7
  let assump_6 := assump_3 assump_13
  apply False.elim assump_6


variable (p2 p7 p6 p3 p5 p4 p0 p1 : Prop)
theorem file22_69902 : (((((p6 ∨ p1) → False) ∨ ((p6 ∨ p3) ∨ (p0 → False))) → (((p3 ∨ True) ∨ (p0 ∨ p7)) ∨ ((True → p4) ∧ (p5 ∧ p2)))) ∨ ((((p2 ∨ p3) → (p0 ∨ p1)) → False) ∧ (((p0 ∧ p5) ∨ (p5 ∨ False)) ∧ ((True → False) → (p5 → p2))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case inl assump_8 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro
      case inr assump_9 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        exact assump_9
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro


variable (p7 p1 p0 p3 p2 p5 p4 p6 : Prop)
theorem file22_70752 : ((((((p0 ∧ p5) ∧ (p3 → p4)) ∧ ((True → p2) → (p3 → False))) ∧ (((p1 ∨ p0) → (False ∧ p3)) ∨ ((False → False) ∨ (p6 → False)))) ∧ ((((p6 → False) → False) → ((p4 → p3) → False)) ∧ (((p7 → p1) → (p4 → p4)) → ((True → False) ∧ (p4 ∧ p5))))) → False) := by
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
            cases assump_5
            case inl assump_20 =>
              cases assump_3
              case intro assump_24 assump_25 =>
                have assump_84 : ((p7 → p1) → (p4 → p4)) := by
                  intro assump_31
                  intro assump_32
                  exact assump_32
                let assump_30 := assump_25 assump_84
                let assump_37 := And.left assump_30
                have assump_85 : True := by
                  apply True.intro
                let assump_38 := assump_37 assump_85
                apply False.elim assump_38
            case inr assump_21 =>
              cases assump_21
              case inl assump_42 =>
                cases assump_3
                case intro assump_46 assump_47 =>
                  have assump_86 : ((p7 → p1) → (p4 → p4)) := by
                    intro assump_53
                    intro assump_54
                    exact assump_54
                  let assump_52 := assump_47 assump_86
                  let assump_59 := And.left assump_52
                  have assump_87 : True := by
                    apply True.intro
                  let assump_60 := assump_59 assump_87
                  apply False.elim assump_60
              case inr assump_43 =>
                cases assump_3
                case intro assump_66 assump_67 =>
                  have assump_88 : ((p7 → p1) → (p4 → p4)) := by
                    intro assump_73
                    intro assump_74
                    exact assump_74
                  let assump_72 := assump_67 assump_88
                  let assump_79 := And.left assump_72
                  have assump_89 : True := by
                    apply True.intro
                  let assump_80 := assump_79 assump_89
                  apply False.elim assump_80


variable (p2 p4 p1 p3 : Prop)
theorem file22_73184 : ((((((True → False) ∧ (p2 ∧ p1)) → False) ∨ (((p4 ∨ p3) → False) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) ∧ (p2 ∧ p1)) → False) ∨ (((p4 ∨ p3) → False) → False)) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : True := by
          apply True.intro
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p4 p7 p5 p6 p0 p1 p3 : Prop)
theorem file22_73820 : (((((p7 ∧ False) ∧ (p1 ∧ p7)) → ((p4 → p0) → (p7 ∨ p4))) → (((p0 ∨ True) → False) → ((p4 → p1) ∨ (True ∨ p5)))) ∨ ((((False → p4) → False) ∧ ((p6 ∧ p0) → False)) ∨ (((p3 → False) → False) ∧ ((p1 → p3) ∧ (False ∨ p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  have assump_16 : (p0 ∨ True) := by
    apply Or.inr
    apply True.intro
  let assump_12 := assump_2 assump_16
  apply False.elim assump_12


variable (p5 : Prop)
theorem file22_74314 : (((((False → p5) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : (((False → p5) → False) → False) := by
    intro assump_5
    have assump_19 : (False → p5) := by
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p6 p3 p7 p4 p0 p1 p5 : Prop)
theorem file22_74757 : ((((((True ∨ p6) → (True → True)) ∨ ((p7 ∧ p4) ∧ (False → p1))) ∨ (((p0 → p6) ∧ (p3 → False)) → ((p3 → False) ∨ (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_10 : ((((True ∨ p6) → (True → True)) ∨ ((p7 ∧ p4) ∧ (False → p1))) ∨ (((p0 → p6) ∧ (p3 → False)) → ((p3 → False) ∨ (p5 → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    apply True.intro
  let assump_4 := assump_1 assump_10
  apply False.elim assump_4


variable (p7 p2 p4 : Prop)
theorem file22_75286 : (((((p4 ∧ p7) → False) → False) ∧ (((p7 → p7) ∨ (p4 ∧ p2)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : ((p7 → p7) ∨ (p4 ∧ p2)) := by
      apply Or.inl
      intro assump_9
      exact assump_9
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p4 p6 p0 p2 p5 : Prop)
theorem file22_75676 : ((((((False → p6) ∧ (p4 ∧ p2)) ∨ ((False ∧ p5) → (p0 → p0))) → (((False → False) → False) → False)) → False) → False) := by
  intro assump_16
  have assump_59 : ((((False → p6) ∧ (p4 ∧ p2)) ∨ ((False ∧ p5) → (p0 → p0))) → (((False → False) → False) → False)) := by
    intro assump_20
    intro assump_21
    cases assump_20
    case inl assump_24 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        cases assump_27
        case intro assump_30 assump_31 =>
          have assump_60 : (False → False) := by
            intro assump_40
            apply False.elim assump_40
          let assump_39 := assump_21 assump_60
          apply False.elim assump_39
    case inr assump_25 =>
      have assump_61 : (False → False) := by
        intro assump_50
        apply False.elim assump_50
      let assump_49 := assump_21 assump_61
      apply False.elim assump_49
  let assump_19 := assump_16 assump_59
  apply False.elim assump_19


variable (p3 p1 p0 p7 p5 p6 p4 : Prop)
theorem file22_76692 : ((((((p4 → False) → False) → ((p1 → False) ∨ (p3 ∧ p7))) ∨ (((p0 → False) ∨ (p1 ∧ p6)) ∨ ((p3 ∨ p7) → (False ∧ p6)))) ∧ ((((True → False) ∧ (p5 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_90 : (((True → False) ∧ (p5 ∧ False)) → False) := by
        intro assump_11
        cases assump_11
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            apply False.elim assump_17
      let assump_10 := assump_3 assump_90
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_25 =>
        cases assump_25
        case inl assump_27 =>
          have assump_91 : (((True → False) ∧ (p5 ∧ False)) → False) := by
            intro assump_34
            cases assump_34
            case intro assump_35 assump_36 =>
              cases assump_36
              case intro assump_39 assump_40 =>
                apply False.elim assump_40
          let assump_33 := assump_3 assump_91
          apply False.elim assump_33
        case inr assump_28 =>
          cases assump_28
          case intro assump_48 assump_49 =>
            have assump_92 : (((True → False) ∧ (p5 ∧ False)) → False) := by
              intro assump_57
              cases assump_57
              case intro assump_58 assump_59 =>
                cases assump_59
                case intro assump_62 assump_63 =>
                  apply False.elim assump_63
            let assump_56 := assump_3 assump_92
            apply False.elim assump_56
      case inr assump_26 =>
        have assump_93 : (((True → False) ∧ (p5 ∧ False)) → False) := by
          intro assump_76
          cases assump_76
          case intro assump_77 assump_78 =>
            cases assump_78
            case intro assump_81 assump_82 =>
              apply False.elim assump_82
        let assump_75 := assump_3 assump_93
        apply False.elim assump_75


variable (p2 p7 p1 p3 p6 p4 : Prop)
theorem file22_78796 : ((((((True → False) ∧ (p2 → p6)) → ((p4 → p4) ∨ (p3 → p7))) ∨ (((p6 → p7) → False) ∨ ((True ∨ p1) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True → False) ∧ (p2 → p6)) → ((p4 → p4) ∨ (p3 → p7))) ∨ (((p6 → p7) → False) ∨ ((True ∨ p1) → False))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      exact assump_12
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p4 p3 p7 p0 p2 p1 : Prop)
theorem file22_79357 : (((((p7 ∧ p2) ∧ (p3 ∧ p2)) → False) ∧ (((p0 → True) ∧ (p0 → False)) ∧ ((True → p3) → (False ∧ p3)))) → ((((False → False) ∨ (p4 → False)) ∧ ((True ∨ p7) → (p4 → False))) → (((p0 ∧ False) ∧ (p1 ∧ True)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      apply False.elim assump_7


variable (p7 p5 p3 p4 : Prop)
theorem file22_79819 : (((((p4 → False) ∨ (p5 → p3)) → ((p3 → p4) ∧ (p7 ∧ p7))) ∧ (((p5 ∧ p5) ∧ (False → p7)) ∧ ((p7 ∨ False) ∧ (False ∨ False)))) → False) := by
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
            case inl assump_20 =>
              cases assump_19
              case inl assump_24 =>
                apply False.elim assump_24
              case inr assump_25 =>
                apply False.elim assump_25
            case inr assump_21 =>
              apply False.elim assump_21


variable (p6 p2 p4 p5 p3 p0 p1 p7 : Prop)
theorem file22_80665 : (((((p0 → p6) ∧ (p1 → False)) ∨ ((True ∨ p3) → (p1 → p3))) → (((p3 ∧ p3) → False) → False)) → ((((p4 ∧ False) ∧ (p4 ∨ p1)) ∧ ((p6 ∧ p5) → False)) ∨ (((p2 ∨ p5) → False) → ((False ∧ p1) → (p7 ∨ True))))) := by
  intro assump_5
  apply Or.inr
  intro assump_8
  intro assump_9
  cases assump_9
  case intro assump_10 assump_11 =>
    apply False.elim assump_10


variable (p7 p0 p3 p5 p4 p6 : Prop)
theorem file22_81084 : ((((((p3 ∧ p4) ∧ (p0 ∨ p7)) → ((p4 → False) → (p5 → p6))) ∨ (((p5 → True) → (p0 ∧ p7)) ∧ ((p0 ∧ p3) → False))) → False) → False) := by
  intro assump_15
  have assump_57 : ((((p3 ∧ p4) ∧ (p0 ∨ p7)) → ((p4 → False) → (p5 → p6))) ∨ (((p5 → True) → (p0 ∧ p7)) ∧ ((p0 ∧ p3) → False))) := by
    apply Or.inl
    intro assump_19
    intro assump_20
    intro assump_21
    cases assump_19
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_27
        case inl assump_34 =>
          have assump_58 : p4 := by
            exact assump_29
          let assump_41 := assump_20 assump_58
          apply False.elim assump_41
        case inr assump_35 =>
          have assump_59 : p4 := by
            exact assump_29
          let assump_50 := assump_20 assump_59
          apply False.elim assump_50
  let assump_18 := assump_15 assump_57
  apply False.elim assump_18


variable (p3 p0 p7 : Prop)
theorem file22_82067 : (((((p0 ∨ p0) ∨ (p0 → False)) → False) ∧ (((p7 ∧ p3) ∧ (p3 → p0)) ∨ ((True ∨ p0) ∨ (p7 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          have assump_79 : ((p0 ∨ p0) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_23
            have assump_80 : ((p0 ∨ p0) ∨ (p0 → False)) := by
              apply Or.inl
              apply Or.inl
              exact assump_23
            let assump_31 := assump_2 assump_80
            apply False.elim assump_31
          let assump_22 := assump_2 assump_79
          apply False.elim assump_22
    case inr assump_7 =>
      cases assump_7
      case inl assump_38 =>
        cases assump_38
        case inl assump_40 =>
          have assump_81 : ((p0 ∨ p0) ∨ (p0 → False)) := by
            apply Or.inr
            intro assump_45
            have assump_82 : ((p0 ∨ p0) ∨ (p0 → False)) := by
              apply Or.inl
              apply Or.inl
              exact assump_45
            let assump_49 := assump_2 assump_82
            apply False.elim assump_49
          let assump_44 := assump_2 assump_81
          apply False.elim assump_44
        case inr assump_41 =>
          have assump_83 : ((p0 ∨ p0) ∨ (p0 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_41
          let assump_59 := assump_2 assump_83
          apply False.elim assump_59
      case inr assump_39 =>
        have assump_84 : ((p0 ∨ p0) ∨ (p0 → False)) := by
          apply Or.inr
          intro assump_67
          have assump_85 : ((p0 ∨ p0) ∨ (p0 → False)) := by
            apply Or.inl
            apply Or.inl
            exact assump_67
          let assump_72 := assump_2 assump_85
          apply False.elim assump_72
        let assump_66 := assump_2 assump_84
        apply False.elim assump_66


variable (p4 p3 p5 p7 p6 : Prop)
theorem file22_84146 : (((((True ∧ True) → False) ∧ ((True ∧ True) → (p3 ∧ p7))) → (((p6 → False) ∨ (p3 → False)) → ((p6 ∧ False) → False))) ∧ ((((p4 → True) ∧ (p3 → False)) → ((False → False) ∨ (p5 ∨ p4))) ∨ (((p5 ∧ p7) ∧ (p4 → p7)) → False))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    apply False.elim assump_5
  apply Or.inl
  intro assump_10
  cases assump_10
  case intro assump_11 assump_12 =>
    apply Or.inl
    intro assump_17
    apply False.elim assump_17


variable (p7 p6 p4 p3 : Prop)
theorem file22_84733 : ((((((False → False) ∨ (p6 → False)) → False) → (((p3 → False) → (p6 → False)) → ((p7 → p4) ∧ (p7 ∧ False)))) → False) → False) := by
  intro assump_1
  have assump_46 : ((((False → False) ∨ (p6 → False)) → False) → (((p3 → False) → (p6 → False)) → ((p7 → p4) ∧ (p7 ∧ False)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    have assump_47 : ((False → False) ∨ (p6 → False)) := by
      apply Or.inl
      intro assump_15
      apply False.elim assump_15
    let assump_14 := assump_5 assump_47
    apply False.elim assump_14
    apply And.intro
    have assump_48 : ((False → False) ∨ (p6 → False)) := by
      apply Or.inl
      intro assump_26
      apply False.elim assump_26
    let assump_25 := assump_5 assump_48
    apply False.elim assump_25
    have assump_49 : ((False → False) ∨ (p6 → False)) := by
      apply Or.inl
      intro assump_37
      apply False.elim assump_37
    let assump_36 := assump_5 assump_49
    apply False.elim assump_36
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4


variable (p6 p2 p7 p3 p4 : Prop)
theorem file22_85851 : (((((p2 → False) → False) → False) → (((False → p4) ∨ (p7 ∨ p4)) ∨ ((p4 ∧ p6) ∧ (False ∨ p7)))) ∨ ((((p3 → False) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply False.elim assump_4


variable (p2 : Prop)
theorem file22_86151 : (((((False ∨ p2) ∧ (True → False)) → False) → False) → False) := by
  intro assump_11
  have assump_33 : (((False ∨ p2) ∧ (True → False)) → False) := by
    intro assump_15
    cases assump_15
    case intro assump_16 assump_17 =>
      cases assump_16
      case inl assump_18 =>
        apply False.elim assump_18
      case inr assump_19 =>
        have assump_34 : True := by
          apply True.intro
        let assump_26 := assump_17 assump_34
        apply False.elim assump_26
  let assump_14 := assump_11 assump_33
  apply False.elim assump_14


variable (p2 p0 p3 p5 p6 p7 p1 : Prop)
theorem file22_86769 : (((((p6 ∧ p1) → (p3 ∨ p7)) ∨ ((p5 ∨ True) → (p5 → False))) → (((p6 ∨ p2) ∨ (p7 ∨ True)) ∧ ((True ∧ p0) → (False ∨ p0)))) ∨ ((((p6 → p3) ∧ (p2 ∧ p5)) ∨ ((False ∧ p6) ∧ (p1 → p0))) ∨ (((True → p3) → (False ∨ False)) → ((True ∧ p1) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  cases assump_1
  case inl assump_2 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  case inr assump_3 =>
    apply Or.inr
    apply Or.inr
    apply True.intro
  intro assump_8
  cases assump_8
  case intro assump_9 assump_10 =>
    cases assump_1
    case inl assump_15 =>
      apply Or.inr
      exact assump_10
    case inr assump_16 =>
      apply Or.inr
      exact assump_10


variable (p1 p5 p4 p2 p0 p6 p7 p3 : Prop)
theorem file22_87527 : (((((p3 ∨ p2) ∧ (True ∧ p6)) → False) ∧ (((p6 ∨ p1) → (p6 ∨ p0)) → ((p2 ∨ p7) ∨ (p5 ∧ False)))) → ((((p4 → p4) → False) → False) ∨ (((p4 → p1) → False) ∧ ((p4 ∧ p7) ∧ (p7 → p6))))) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    apply Or.inl
    intro assump_12
    have assump_22 : (p4 → p4) := by
      intro assump_16
      exact assump_16
    let assump_15 := assump_12 assump_22
    apply False.elim assump_15


variable (p1 : Prop)
theorem file22_88017 : ((((((True ∨ False) ∨ (p1 → False)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ False) ∨ (p1 → False)) → False) → False) := by
    intro assump_5
    have assump_16 : ((True ∨ False) ∨ (p1 → False)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p7 p2 p6 p1 p0 p3 p4 : Prop)
theorem file22_88525 : (((((p2 → p4) ∨ (True → p0)) ∨ ((p0 → False) → (p1 ∨ p1))) → (((p1 ∧ False) → (p2 ∨ p6)) ∨ ((p4 → True) → (p0 ∧ p4)))) → ((((p2 ∧ False) ∨ (p2 ∧ p3)) ∨ ((True → False) → (True → False))) → (((p0 → p0) ∨ (p3 → p7)) ∨ ((True ∨ True) ∧ (False ∧ p7))))) := by
  intro assump_22
  intro assump_23
  cases assump_23
  case inl assump_24 =>
    cases assump_24
    case inl assump_26 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        apply False.elim assump_29
    case inr assump_27 =>
      cases assump_27
      case intro assump_34 assump_35 =>
        apply Or.inl
        apply Or.inl
        intro assump_42
        exact assump_42
  case inr assump_25 =>
    apply Or.inl
    apply Or.inl
    intro assump_49
    exact assump_49


variable (p4 p5 p2 p0 p6 p1 p7 p3 : Prop)
theorem file22_89344 : (((((p4 ∧ p7) → False) ∨ ((p7 → False) → (p6 ∧ True))) ∧ (((p1 → p1) ∨ (True ∨ p5)) → False)) → ((((p1 ∨ p2) → False) → False) → (((p0 → False) ∨ (p3 → p2)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_1
    case intro assump_10 assump_11 =>
      cases assump_10
      case inl assump_12 =>
        have assump_66 : ((p1 → p1) ∨ (True ∨ p5)) := by
          apply Or.inl
          intro assump_19
          exact assump_19
        let assump_18 := assump_11 assump_66
        apply False.elim assump_18
      case inr assump_13 =>
        have assump_67 : ((p1 → p1) ∨ (True ∨ p5)) := by
          apply Or.inl
          intro assump_30
          exact assump_30
        let assump_29 := assump_11 assump_67
        apply False.elim assump_29
  case inr assump_5 =>
    cases assump_1
    case intro assump_40 assump_41 =>
      cases assump_40
      case inl assump_42 =>
        have assump_68 : ((p1 → p1) ∨ (True ∨ p5)) := by
          apply Or.inl
          intro assump_49
          exact assump_49
        let assump_48 := assump_41 assump_68
        apply False.elim assump_48
      case inr assump_43 =>
        have assump_69 : ((p1 → p1) ∨ (True ∨ p5)) := by
          apply Or.inl
          intro assump_60
          exact assump_60
        let assump_59 := assump_41 assump_69
        apply False.elim assump_59


variable (p7 p4 p2 : Prop)
theorem file22_90801 : ((((((True → False) → False) → False) → (((p2 ∧ p4) ∨ (p7 ∨ p4)) → False)) → False) → False) := by
  intro assump_1
  have assump_63 : ((((True → False) → False) → False) → (((p2 ∧ p4) ∨ (p7 ∨ p4)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        have assump_64 : ((True → False) → False) := by
          intro assump_18
          have assump_65 : True := by
            apply True.intro
          let assump_21 := assump_18 assump_65
          apply False.elim assump_21
        let assump_17 := assump_5 assump_64
        apply False.elim assump_17
    case inr assump_8 =>
      cases assump_8
      case inl assump_28 =>
        have assump_66 : ((True → False) → False) := by
          intro assump_35
          have assump_67 : True := by
            apply True.intro
          let assump_38 := assump_35 assump_67
          apply False.elim assump_38
        let assump_34 := assump_5 assump_66
        apply False.elim assump_34
      case inr assump_29 =>
        have assump_68 : ((True → False) → False) := by
          intro assump_50
          have assump_69 : True := by
            apply True.intro
          let assump_53 := assump_50 assump_69
          apply False.elim assump_53
        let assump_49 := assump_5 assump_68
        apply False.elim assump_49
  let assump_4 := assump_1 assump_63
  apply False.elim assump_4


variable (p0 p3 p6 p4 p7 : Prop)
theorem file22_92317 : (((((p3 ∧ p7) ∧ (p3 → False)) → ((p0 ∧ False) ∨ (p4 ∨ p6))) → False) → False) := by
  intro assump_1
  have assump_23 : (((p3 ∧ p7) ∧ (p3 → False)) → ((p0 ∧ False) ∨ (p4 ∨ p6))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_24 : p3 := by
          exact assump_8
        let assump_16 := assump_7 assump_24
        apply False.elim assump_16
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p3 p4 p6 p0 p1 p5 p2 : Prop)
theorem file22_92900 : (((((p1 ∨ False) ∧ (p5 → False)) ∧ ((p5 ∨ p3) ∧ (p4 ∧ p0))) ∧ (((p5 ∨ True) ∨ (p1 ∧ p2)) → False)) → ((((p1 ∨ False) ∨ (p3 ∧ p3)) ∨ ((p0 → False) ∨ (p1 → p4))) ∨ (((p6 → False) ∨ (p5 → False)) → ((p2 → True) ∧ (False → p2))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case inl assump_16 =>
              cases assump_15
              case intro assump_20 assump_21 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_8
            case inr assump_17 =>
              cases assump_15
              case intro assump_30 assump_31 =>
                apply Or.inl
                apply Or.inl
                apply Or.inl
                apply Or.inl
                exact assump_8
        case inr assump_9 =>
          apply False.elim assump_9


variable (p5 p3 p4 p1 p0 p2 : Prop)
theorem file22_94107 : ((((((p5 → True) ∨ (p1 ∨ p4)) ∧ ((True → False) → (p2 ∧ p4))) ∧ (((False ∧ p3) ∧ (True → p4)) ∧ ((True ∧ p1) → False))) ∧ ((((p4 → p2) ∧ (False → False)) ∧ ((p0 ∨ p0) ∨ (p2 → False))) ∨ (((p5 ∧ False) ∧ (p0 → True)) → ((p1 ∧ True) ∧ (p0 ∧ p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_5
          case intro assump_14 assump_15 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                apply False.elim assump_18
        case inr assump_9 =>
          cases assump_9
          case inl assump_22 =>
            cases assump_5
            case intro assump_28 assump_29 =>
              cases assump_28
              case intro assump_30 assump_31 =>
                cases assump_30
                case intro assump_32 assump_33 =>
                  apply False.elim assump_32
          case inr assump_23 =>
            cases assump_5
            case intro assump_40 assump_41 =>
              cases assump_40
              case intro assump_42 assump_43 =>
                cases assump_42
                case intro assump_44 assump_45 =>
                  apply False.elim assump_44


