variable (p3 p7 p0 p4 : Prop)
theorem file79_38 : ((((((p0 ∧ False) → False) ∨ ((p7 → False) ∧ (p3 ∧ True))) ∨ (((p4 ∨ p0) → False) ∨ ((False ∧ p3) ∨ (False → False)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((p0 ∧ False) → False) ∨ ((p7 → False) ∧ (p3 ∧ True))) ∨ (((p4 ∨ p0) → False) ∨ ((False ∧ p3) ∨ (False → False)))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p4 p6 p1 p7 p2 p3 p0 p5 : Prop)
theorem file79_611 : (((((p4 ∧ p7) ∧ (p5 ∨ p3)) → ((p3 ∧ p2) → (False → p5))) ∨ (((p3 ∨ p5) → (True → False)) ∨ ((p0 ∧ p4) ∨ (False ∧ False)))) ∨ ((((p6 → False) ∨ (p3 → p3)) → ((p1 → p5) → False)) ∨ (((p5 ∨ p0) → (p3 → False)) → ((p1 ∧ p5) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply False.elim assump_3


variable (p2 p7 p0 p5 p6 p1 p4 : Prop)
theorem file79_1021 : ((((((p4 ∧ p7) → False) → ((True ∨ p5) ∨ (p7 → p5))) ∨ (((p4 ∨ p0) ∧ (True ∨ p5)) → ((p2 ∨ p5) → (p6 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p4 ∧ p7) → False) → ((True ∨ p5) ∨ (p7 → p5))) ∨ (((p4 ∨ p0) ∧ (True ∨ p5)) → ((p2 ∨ p5) → (p6 ∧ p1)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p6 p0 p2 p5 p3 p7 p1 : Prop)
theorem file79_1524 : ((((((True → False) → (p7 ∨ p3)) ∧ ((p1 ∧ p7) ∧ (False ∧ p0))) → (((p3 ∧ p6) → (p2 ∧ p0)) ∨ ((p5 ∨ p2) → False))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((True → False) → (p7 ∨ p3)) ∧ ((p1 ∧ p7) ∧ (False ∧ p0))) → (((p3 ∧ p6) → (p2 ∧ p0)) ∨ ((p5 ∨ p2) → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_11
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p3 p1 p2 p0 p5 p6 : Prop)
theorem file79_2251 : ((((((True → False) ∧ (p5 → p1)) → False) → (((p0 ∨ True) ∨ (True ∨ p3)) ∧ ((p2 ∧ True) → False))) ∧ ((((p3 → True) → (p6 ∨ p2)) → ((p6 → False) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_17 : (((p3 → True) → (p6 ∨ p2)) → ((p6 → False) → (False → False))) := by
      intro assump_9
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    let assump_8 := assump_3 assump_17
    apply False.elim assump_8


variable (p3 p2 p5 p0 p6 p1 p7 : Prop)
theorem file79_2829 : ((((((p2 ∧ True) ∨ (p6 → p5)) ∧ ((p0 → False) ∧ (True → True))) → (((p7 → False) ∨ (p1 ∧ p7)) → ((p3 → p3) ∨ (p7 ∨ p0)))) → False) → False) := by
  intro assump_1
  have assump_80 : ((((p2 ∧ True) ∨ (p6 → p5)) ∧ ((p0 → False) ∧ (True → True))) → (((p7 → False) ∨ (p1 ∧ p7)) → ((p3 → p3) ∨ (p7 ∨ p0)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            cases assump_12
            case intro assump_21 assump_22 =>
              apply Or.inl
              intro assump_27
              exact assump_27
        case inr assump_14 =>
          cases assump_12
          case intro assump_32 assump_33 =>
            apply Or.inl
            intro assump_38
            exact assump_38
    case inr assump_8 =>
      cases assump_8
      case intro assump_41 assump_42 =>
        cases assump_5
        case intro assump_47 assump_48 =>
          cases assump_47
          case inl assump_49 =>
            cases assump_49
            case intro assump_51 assump_52 =>
              cases assump_48
              case intro assump_57 assump_58 =>
                apply Or.inl
                intro assump_63
                exact assump_63
          case inr assump_50 =>
            cases assump_48
            case intro assump_68 assump_69 =>
              apply Or.inl
              intro assump_74
              exact assump_74
  let assump_4 := assump_1 assump_80
  apply False.elim assump_4


variable (p5 p0 p7 p6 p2 p3 p1 p4 : Prop)
theorem file79_4524 : (((((True → False) ∨ (False ∧ p0)) ∧ ((p7 → p7) → (True → False))) → (((p7 ∧ True) ∨ (p4 ∨ True)) → ((p1 ∧ p5) → (p7 ∧ p0)))) ∨ ((((p6 → True) ∨ (p2 ∧ p3)) ∧ ((False → False) ∧ (p3 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case inl assump_20 =>
            exact assump_12
          case inr assump_21 =>
            cases assump_21
            case intro assump_26 assump_27 =>
              apply False.elim assump_26
    case inr assump_11 =>
      cases assump_11
      case inl assump_30 =>
        cases assump_1
        case intro assump_34 assump_35 =>
          cases assump_34
          case inl assump_36 =>
            have assump_156 : (p7 → p7) := by
              intro assump_43
              exact assump_43
            let assump_42 := assump_35 assump_156
            have assump_157 : True := by
              apply True.intro
            let assump_46 := assump_42 assump_157
            apply False.elim assump_46
          case inr assump_37 =>
            cases assump_37
            case intro assump_50 assump_51 =>
              apply False.elim assump_50
      case inr assump_31 =>
        cases assump_1
        case intro assump_56 assump_57 =>
          cases assump_56
          case inl assump_58 =>
            have assump_158 : (p7 → p7) := by
              intro assump_65
              exact assump_65
            let assump_64 := assump_57 assump_158
            have assump_159 : True := by
              apply True.intro
            let assump_68 := assump_64 assump_159
            apply False.elim assump_68
          case inr assump_59 =>
            cases assump_59
            case intro assump_72 assump_73 =>
              apply False.elim assump_72
  cases assump_3
  case intro assump_76 assump_77 =>
    cases assump_2
    case inl assump_82 =>
      cases assump_82
      case intro assump_84 assump_85 =>
        cases assump_1
        case intro assump_90 assump_91 =>
          cases assump_90
          case inl assump_92 =>
            have assump_160 : (p7 → p7) := by
              intro assump_99
              exact assump_99
            let assump_98 := assump_91 assump_160
            have assump_161 : True := by
              apply True.intro
            let assump_102 := assump_98 assump_161
            apply False.elim assump_102
          case inr assump_93 =>
            cases assump_93
            case intro assump_106 assump_107 =>
              apply False.elim assump_106
    case inr assump_83 =>
      cases assump_83
      case inl assump_110 =>
        cases assump_1
        case intro assump_114 assump_115 =>
          cases assump_114
          case inl assump_116 =>
            have assump_162 : (p7 → p7) := by
              intro assump_123
              exact assump_123
            let assump_122 := assump_115 assump_162
            have assump_163 : True := by
              apply True.intro
            let assump_126 := assump_122 assump_163
            apply False.elim assump_126
          case inr assump_117 =>
            cases assump_117
            case intro assump_130 assump_131 =>
              apply False.elim assump_130
      case inr assump_111 =>
        cases assump_1
        case intro assump_136 assump_137 =>
          cases assump_136
          case inl assump_138 =>
            have assump_164 : (p7 → p7) := by
              intro assump_145
              exact assump_145
            let assump_144 := assump_137 assump_164
            have assump_165 : True := by
              apply True.intro
            let assump_148 := assump_144 assump_165
            apply False.elim assump_148
          case inr assump_139 =>
            cases assump_139
            case intro assump_152 assump_153 =>
              apply False.elim assump_152


variable (p2 p5 p6 p4 p1 p7 p3 p0 : Prop)
theorem file79_8680 : (((((p2 ∨ True) ∨ (p7 ∧ p0)) → ((False ∨ p1) ∧ (False → p2))) → (((p5 ∧ p7) ∧ (p6 → p2)) → ((p5 → False) → (p0 ∨ p1)))) ∨ ((((p6 ∨ p4) → False) ∧ ((p4 → p3) → (False ∧ False))) ∧ (((p1 → False) → (p0 ∨ p5)) ∧ ((p6 → p5) → (p1 → p5))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      have assump_27 : ((p2 ∨ True) ∨ (p7 ∧ p0)) := by
        apply Or.inl
        apply Or.inr
        apply True.intro
      let assump_18 := assump_1 assump_27
      let assump_19 := And.left assump_18
      cases assump_19
      case inl assump_21 =>
        apply False.elim assump_21
      case inr assump_22 =>
        apply Or.inr
        exact assump_22


variable (p1 p3 p4 p2 p0 p5 p6 : Prop)
theorem file79_9521 : (((((p4 ∨ p6) ∨ (p2 → False)) ∧ ((p0 ∧ False) ∨ (True → False))) → False) ∨ ((((p6 → False) → False) → False) ∧ (((p5 → False) → False) ∧ ((p3 ∧ p1) → (False ∧ p0))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_3
        case inl assump_10 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_13
        case inr assump_11 =>
          have assump_56 : True := by
            apply True.intro
          let assump_20 := assump_11 assump_56
          apply False.elim assump_20
      case inr assump_7 =>
        cases assump_3
        case inl assump_26 =>
          cases assump_26
          case intro assump_28 assump_29 =>
            apply False.elim assump_29
        case inr assump_27 =>
          have assump_57 : True := by
            apply True.intro
          let assump_36 := assump_27 assump_57
          apply False.elim assump_36
    case inr assump_5 =>
      cases assump_3
      case inl assump_42 =>
        cases assump_42
        case intro assump_44 assump_45 =>
          apply False.elim assump_45
      case inr assump_43 =>
        have assump_58 : True := by
          apply True.intro
        let assump_52 := assump_43 assump_58
        apply False.elim assump_52


variable (p3 p0 p4 p1 : Prop)
theorem file79_10985 : ((((((True → p3) → False) ∨ ((p1 → True) ∧ (p0 ∧ p3))) → (((p0 ∧ p0) → (p4 ∧ p1)) → ((False ∧ p1) → False))) ∧ ((((False → p0) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → p0) → False) → False) := by
      intro assump_9
      have assump_23 : (False → p0) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p0 p2 p7 p3 p1 p6 : Prop)
theorem file79_11609 : ((((((p2 ∨ p7) ∨ (p6 → True)) ∧ ((p3 ∧ p7) ∧ (p1 → False))) ∨ (((p6 → False) → (p2 ∧ p7)) → ((p3 ∧ True) → (p2 ∨ p7)))) ∧ ((((True → p0) → False) → ((p1 ∨ p0) → (p7 → p7))) → False)) → False) := by
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
          case inl assump_10 =>
            cases assump_7
            case intro assump_14 assump_15 =>
              cases assump_14
              case intro assump_16 assump_17 =>
                have assump_134 : (((True → p0) → False) → ((p1 ∨ p0) → (p7 → p7))) := by
                  intro assump_27
                  intro assump_28
                  intro assump_29
                  cases assump_28
                  case inl assump_32 =>
                    exact assump_29
                  case inr assump_33 =>
                    exact assump_29
                let assump_26 := assump_3 assump_134
                apply False.elim assump_26
          case inr assump_11 =>
            cases assump_7
            case intro assump_47 assump_48 =>
              cases assump_47
              case intro assump_49 assump_50 =>
                have assump_135 : (((True → p0) → False) → ((p1 ∨ p0) → (p7 → p7))) := by
                  intro assump_60
                  intro assump_61
                  intro assump_62
                  cases assump_61
                  case inl assump_65 =>
                    exact assump_62
                  case inr assump_66 =>
                    exact assump_62
                let assump_59 := assump_3 assump_135
                apply False.elim assump_59
        case inr assump_9 =>
          cases assump_7
          case intro assump_80 assump_81 =>
            cases assump_80
            case intro assump_82 assump_83 =>
              have assump_136 : (((True → p0) → False) → ((p1 ∨ p0) → (p7 → p7))) := by
                intro assump_93
                intro assump_94
                intro assump_95
                cases assump_94
                case inl assump_98 =>
                  exact assump_95
                case inr assump_99 =>
                  exact assump_95
              let assump_92 := assump_3 assump_136
              apply False.elim assump_92
    case inr assump_5 =>
      have assump_137 : (((True → p0) → False) → ((p1 ∨ p0) → (p7 → p7))) := by
        intro assump_116
        intro assump_117
        intro assump_118
        cases assump_117
        case inl assump_121 =>
          exact assump_118
        case inr assump_122 =>
          exact assump_118
      let assump_115 := assump_3 assump_137
      apply False.elim assump_115


variable (p6 p1 p0 p2 : Prop)
theorem file79_14446 : (((((True ∧ p2) ∨ (p1 ∧ p6)) ∨ ((False ∧ p1) → (p0 → p1))) → False) → False) := by
  intro assump_1
  have assump_16 : (((True ∧ p2) ∨ (p1 ∧ p6)) ∨ ((False ∧ p1) → (p0 → p1))) := by
    apply Or.inr
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p7 p1 p3 p2 p4 p5 p6 : Prop)
theorem file79_14899 : (((((p4 ∨ True) ∨ (p2 ∨ p2)) → False) → False) ∧ ((((p3 ∧ False) ∨ (p2 ∨ p5)) ∧ ((p6 ∧ p7) → (p6 → p6))) → (((p1 → True) → False) → False))) := by
  apply And.intro
  intro assump_1
  have assump_46 : ((p4 ∨ True) ∨ (p2 ∨ p2)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_46
  apply False.elim assump_4
  intro assump_8
  intro assump_9
  cases assump_8
  case intro assump_12 assump_13 =>
    cases assump_12
    case inl assump_14 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
    case inr assump_15 =>
      cases assump_15
      case inl assump_22 =>
        have assump_47 : (p1 → True) := by
          intro assump_31
          apply True.intro
        let assump_30 := assump_9 assump_47
        apply False.elim assump_30
      case inr assump_23 =>
        have assump_48 : (p1 → True) := by
          intro assump_42
          apply True.intro
        let assump_41 := assump_9 assump_48
        apply False.elim assump_41


variable (p3 p6 p0 p7 p1 p4 p5 : Prop)
theorem file79_15999 : ((((((False ∨ p7) ∨ (p1 → p3)) ∧ ((True → p0) → (p1 → False))) → (((p5 ∧ p4) ∧ (False ∧ p5)) → ((p7 → False) ∧ (p6 ∨ p6)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((False ∨ p7) ∨ (p1 → p3)) ∧ ((True → p0) → (p1 → False))) → (((p5 ∧ p4) ∧ (False ∧ p5)) → ((p7 → False) ∧ (p6 ∨ p6)))) := by
    intro assump_5
    intro assump_6
    apply And.intro
    intro assump_7
    cases assump_6
    case intro assump_10 assump_11 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_11
        case intro assump_18 assump_19 =>
          apply False.elim assump_18
    cases assump_6
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_23
        case intro assump_30 assump_31 =>
          apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p0 p6 p5 p4 p7 p2 : Prop)
theorem file79_16957 : (((((False ∧ p4) ∧ (False → p5)) ∧ ((p2 → True) ∧ (False → False))) ∧ (((p7 ∧ p5) ∧ (p6 ∧ p4)) ∨ ((p6 → p0) ∧ (True ∧ p2)))) → False) := by
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


variable (p0 p5 p2 p1 p7 : Prop)
theorem file79_17435 : ((((((True → False) → (p5 → False)) ∨ ((p2 ∨ False) ∨ (p5 ∨ p5))) ∨ (((p1 ∨ p7) ∧ (True → p2)) ∨ ((p0 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_18 : ((((True → False) → (p5 → False)) ∨ ((p2 ∨ False) ∨ (p5 ∨ p5))) ∨ (((p1 ∨ p7) ∧ (True → p2)) ∨ ((p0 → False) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    intro assump_6
    have assump_19 : True := by
      apply True.intro
    let assump_11 := assump_5 assump_19
    apply False.elim assump_11
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p3 p4 p5 p2 p1 p6 p7 : Prop)
theorem file79_18069 : (((((p2 → False) ∨ (p4 → p2)) → ((p6 → False) ∧ (p2 → p3))) ∨ (((p3 → False) → False) → ((p1 → False) ∧ (p7 ∧ p4)))) → ((((False ∧ p4) ∧ (False → False)) ∧ ((p6 → False) ∧ (p2 → p5))) → (((p5 ∧ p3) ∨ (p6 ∨ p4)) ∨ ((p5 → False) → (False ∧ True))))) := by
  intro assump_53
  intro assump_54
  cases assump_54
  case intro assump_55 assump_56 =>
    cases assump_55
    case intro assump_57 assump_58 =>
      cases assump_57
      case intro assump_59 assump_60 =>
        apply False.elim assump_59


variable (p3 p4 p2 p0 p1 : Prop)
theorem file79_18625 : ((((((p3 → False) → False) ∨ ((p1 → p0) ∨ (p3 ∧ p3))) → False) ∧ ((((p0 → p0) ∨ (False ∨ p1)) → False) ∧ (((False ∧ p2) ∧ (p4 → False)) ∨ ((p0 → False) ∨ (False ∧ p2))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
      case inr assump_11 =>
        cases assump_11
        case inl assump_18 =>
          have assump_34 : ((p0 → p0) ∨ (False ∨ p1)) := by
            apply Or.inl
            intro assump_24
            exact assump_24
          let assump_23 := assump_6 assump_34
          apply False.elim assump_23
        case inr assump_19 =>
          cases assump_19
          case intro assump_30 assump_31 =>
            apply False.elim assump_30


variable (p2 p3 p0 p4 p1 p5 p7 : Prop)
theorem file79_19666 : (((((p2 ∧ p0) ∧ (p1 → False)) ∧ ((p0 → p2) → (p4 → p7))) → (((p4 ∧ p7) ∨ (False → p4)) → ((p4 → p7) ∧ (p1 → p0)))) ∨ ((((p5 → p7) → (False ∧ p4)) ∧ ((p7 ∧ p3) → (p2 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_1
      case intro assump_14 assump_15 =>
        cases assump_14
        case intro assump_16 assump_17 =>
          cases assump_16
          case intro assump_18 assump_19 =>
            exact assump_9
  case inr assump_7 =>
    cases assump_1
    case intro assump_30 assump_31 =>
      cases assump_30
      case intro assump_32 assump_33 =>
        cases assump_32
        case intro assump_34 assump_35 =>
          have assump_91 : (p0 → p2) := by
            intro assump_45
            exact assump_34
          let assump_44 := assump_31 assump_91
          have assump_92 : p4 := by
            exact assump_3
          let assump_48 := assump_44 assump_92
          exact assump_48
  intro assump_50
  cases assump_2
  case inl assump_53 =>
    cases assump_53
    case intro assump_55 assump_56 =>
      cases assump_1
      case intro assump_61 assump_62 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          cases assump_63
          case intro assump_65 assump_66 =>
            exact assump_66
  case inr assump_54 =>
    cases assump_1
    case intro assump_77 assump_78 =>
      cases assump_77
      case intro assump_79 assump_80 =>
        cases assump_79
        case intro assump_81 assump_82 =>
          exact assump_82


variable (p6 p7 p4 p2 p1 p0 : Prop)
theorem file79_21388 : ((((((p4 ∨ p2) → False) ∨ ((False ∧ p2) → False)) → (((p4 → p4) → (p7 → False)) ∨ ((True ∨ False) → False))) ∧ ((((p6 → p6) ∧ (p0 → p0)) ∧ ((p6 ∨ p1) → (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((p6 → p6) ∧ (p0 → p0)) ∧ ((p6 ∨ p1) → (False → False))) := by
      apply And.intro
      apply And.intro
      intro assump_9
      exact assump_9
      intro assump_12
      exact assump_12
      intro assump_15
      intro assump_16
      apply False.elim assump_16
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p4 p0 p2 p6 p7 p1 : Prop)
theorem file79_22072 : (((((p1 ∨ p1) → False) → ((True → p7) → (p0 → p7))) → (((p6 ∧ False) ∧ (p0 → False)) ∧ ((p2 → False) ∨ (p2 → p4)))) → False) := by
  intro assump_1
  have assump_24 : (((p1 ∨ p1) → False) → ((True → p7) → (p0 → p7))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    have assump_25 : True := by
      apply True.intro
    let assump_15 := assump_6 assump_25
    exact assump_15
  let assump_4 := assump_1 assump_24
  let assump_17 := And.left assump_4
  let assump_18 := And.left assump_17
  let assump_19 := And.right assump_18
  apply False.elim assump_19


variable (p1 p3 p4 p7 p0 : Prop)
theorem file79_22704 : (((((p7 → False) ∧ (p0 ∨ p7)) ∧ ((False ∧ p1) ∨ (True → False))) ∧ (((False ∧ p4) ∧ (False ∨ p3)) ∨ ((p3 → p1) ∧ (p4 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_5
          case inl assump_14 =>
            cases assump_14
            case intro assump_16 assump_17 =>
              apply False.elim assump_16
          case inr assump_15 =>
            cases assump_3
            case inl assump_22 =>
              cases assump_22
              case intro assump_24 assump_25 =>
                cases assump_24
                case intro assump_26 assump_27 =>
                  apply False.elim assump_26
            case inr assump_23 =>
              cases assump_23
              case intro assump_30 assump_31 =>
                have assump_72 : True := by
                  apply True.intro
                let assump_38 := assump_15 assump_72
                apply False.elim assump_38
        case inr assump_11 =>
          cases assump_5
          case inl assump_44 =>
            cases assump_44
            case intro assump_46 assump_47 =>
              apply False.elim assump_46
          case inr assump_45 =>
            cases assump_3
            case inl assump_52 =>
              cases assump_52
              case intro assump_54 assump_55 =>
                cases assump_54
                case intro assump_56 assump_57 =>
                  apply False.elim assump_56
            case inr assump_53 =>
              cases assump_53
              case intro assump_60 assump_61 =>
                have assump_73 : True := by
                  apply True.intro
                let assump_68 := assump_45 assump_73
                apply False.elim assump_68


variable (p0 p5 p2 p7 p6 : Prop)
theorem file79_24684 : (((((p2 ∧ False) → False) ∨ ((p0 ∧ True) → False)) → False) → ((((p5 ∧ True) → False) ∨ ((p6 ∧ False) ∨ (p2 → p0))) ∨ (((p2 ∨ p7) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_23 : (((p2 ∧ False) → False) ∨ ((p0 ∧ True) → False)) := by
      apply Or.inl
      intro assump_13
      cases assump_13
      case intro assump_14 assump_15 =>
        apply False.elim assump_15
    let assump_12 := assump_1 assump_23
    apply False.elim assump_12


variable (p4 p1 p6 p7 p5 : Prop)
theorem file79_25297 : (((((p7 → True) ∧ (p4 ∧ True)) ∧ ((p1 ∧ p1) → (p1 → False))) ∧ (((p5 ∧ False) → False) ∧ ((p4 ∨ p6) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            have assump_28 : (p4 ∨ p6) := by
              apply Or.inl
              exact assump_10
            let assump_24 := assump_19 assump_28
            apply False.elim assump_24


variable (p5 : Prop)
theorem file79_25974 : (((((True → False) → False) → False) ∧ (((False → False) → (p5 → False)) ∧ ((p5 ∧ p5) ∧ (True → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case intro assump_12 assump_13 =>
          have assump_24 : True := by
            apply True.intro
          let assump_20 := assump_11 assump_24
          apply False.elim assump_20


variable (p7 p0 p5 p4 p3 : Prop)
theorem file79_26553 : ((((((p4 ∧ p3) ∧ (p4 ∧ p4)) → ((False → False) → False)) ∨ (((True → p0) → (p7 ∧ p3)) → False)) ∧ ((((p5 → False) → False) → ((False ∧ p4) → False)) → False)) → False) := by
  intro assump_12
  cases assump_12
  case intro assump_13 assump_14 =>
    cases assump_13
    case inl assump_15 =>
      have assump_45 : (((p5 → False) → False) → ((False ∧ p4) → False)) := by
        intro assump_22
        intro assump_23
        cases assump_23
        case intro assump_24 assump_25 =>
          apply False.elim assump_24
      let assump_21 := assump_14 assump_45
      apply False.elim assump_21
    case inr assump_16 =>
      have assump_46 : (((p5 → False) → False) → ((False ∧ p4) → False)) := by
        intro assump_36
        intro assump_37
        cases assump_37
        case intro assump_38 assump_39 =>
          apply False.elim assump_38
      let assump_35 := assump_14 assump_46
      apply False.elim assump_35


variable (p6 p0 p2 p5 p3 p1 : Prop)
theorem file79_27543 : (((((p5 → p2) → False) ∨ ((p1 ∧ False) → False)) ∨ (((p6 → False) → False) → ((p2 ∧ p2) → False))) → ((((True → False) → False) ∧ ((p3 ∨ p3) → (p3 ∨ True))) ∨ (((p3 → p1) ∨ (p0 ∧ False)) ∧ ((p0 → False) ∧ (True ∧ p3))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case inl assump_4 =>
      apply Or.inl
      apply And.intro
      intro assump_8
      have assump_54 : True := by
        apply True.intro
      let assump_11 := assump_8 assump_54
      apply False.elim assump_11
      intro assump_15
      cases assump_15
      case inl assump_16 =>
        apply Or.inl
        exact assump_16
      case inr assump_17 =>
        apply Or.inl
        exact assump_17
    case inr assump_5 =>
      apply Or.inl
      apply And.intro
      intro assump_24
      have assump_55 : True := by
        apply True.intro
      let assump_27 := assump_24 assump_55
      apply False.elim assump_27
      intro assump_31
      cases assump_31
      case inl assump_32 =>
        apply Or.inl
        exact assump_32
      case inr assump_33 =>
        apply Or.inl
        exact assump_33
  case inr assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_40
    have assump_56 : True := by
      apply True.intro
    let assump_43 := assump_40 assump_56
    apply False.elim assump_43
    intro assump_47
    cases assump_47
    case inl assump_48 =>
      apply Or.inl
      exact assump_48
    case inr assump_49 =>
      apply Or.inl
      exact assump_49


variable (p0 p3 p4 p7 p6 p5 : Prop)
theorem file79_29111 : (((((p5 ∨ p5) ∨ (p5 ∨ p0)) → ((p3 → True) → (False ∨ p7))) → (((p7 ∧ True) → False) → ((p7 ∨ p3) → (p4 → p4)))) ∨ ((((p6 ∧ p0) → False) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_3
  case inl assump_7 =>
    exact assump_4
  case inr assump_8 =>
    exact assump_4


variable (p0 p1 p2 p4 p3 p7 : Prop)
theorem file79_29516 : (((((p3 ∨ p1) → (p7 → True)) ∧ ((p7 → False) ∧ (p0 ∧ p4))) ∧ (((False ∨ p4) → False) ∧ ((p4 ∧ p2) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_3
          case intro assump_18 assump_19 =>
            have assump_29 : (False ∨ p4) := by
              apply Or.inr
              exact assump_13
            let assump_25 := assump_18 assump_29
            apply False.elim assump_25


variable (p6 p0 p1 p4 p3 p2 : Prop)
theorem file79_30209 : (((((p0 → p3) ∨ (p0 ∨ True)) → ((p2 → True) ∨ (p0 → True))) ∨ (((True ∧ p6) ∧ (False → False)) ∨ ((p2 ∧ p4) ∨ (p0 → False)))) ∨ ((((p6 → p0) ∨ (p1 → False)) ∨ ((p6 → p6) ∧ (p6 → p3))) ∨ (((p0 → False) → (p4 ∧ p0)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    apply True.intro
  case inr assump_3 =>
    cases assump_3
    case inl assump_7 =>
      apply Or.inl
      intro assump_11
      apply True.intro
    case inr assump_8 =>
      apply Or.inl
      intro assump_14
      apply True.intro


variable (p1 p4 p3 p6 p7 p0 p5 : Prop)
theorem file79_30867 : ((((((p0 → False) ∨ (p3 ∨ p6)) ∨ ((p5 ∧ p0) → (p4 → False))) → (((p7 → p1) ∨ (p1 → False)) → ((False → False) → (p6 ∨ True)))) ∧ ((((p0 → False) ∨ (p7 → p7)) → False) ∧ (((True → False) → (p7 → p1)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_26 : ((True → False) → (p7 → p1)) := by
        intro assump_13
        intro assump_14
        have assump_27 : True := by
          apply True.intro
        let assump_19 := assump_13 assump_27
        apply False.elim assump_19
      let assump_12 := assump_7 assump_26
      apply False.elim assump_12


variable (p5 p6 p1 p2 p3 p7 p4 : Prop)
theorem file79_31602 : (((((p2 ∧ p7) ∧ (p7 → False)) ∧ ((p7 ∧ True) ∧ (p3 → p5))) → (((True ∨ p1) → (p4 ∨ p6)) ∨ ((True ∨ False) → (p3 → False)))) ∨ ((((False → False) ∨ (p2 → False)) → ((False → False) ∧ (p6 → False))) → False)) := by
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
            apply Or.inl
            intro assump_24
            cases assump_24
            case inl assump_25 =>
              have assump_44 : p7 := by
                exact assump_16
              let assump_31 := assump_5 assump_44
              apply False.elim assump_31
            case inr assump_26 =>
              have assump_45 : p7 := by
                exact assump_16
              let assump_40 := assump_5 assump_45
              apply False.elim assump_40


variable (p3 p0 p6 p1 p4 p2 p5 p7 : Prop)
theorem file79_32688 : ((((((p2 → False) → False) → ((p4 → False) → (p1 → p7))) ∧ (((p1 ∨ p3) ∧ (False ∨ False)) ∧ ((p4 ∨ True) → (p5 → p2)))) ∧ ((((p7 → False) → (False ∧ p3)) ∧ ((p5 → p5) → (p4 → False))) ∨ (((p0 → p3) ∨ (False → True)) ∨ ((p6 ∨ p3) → (p7 ∧ p7))))) → False) := by
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
              apply False.elim assump_17
          case inr assump_13 =>
            cases assump_11
            case inl assump_24 =>
              apply False.elim assump_24
            case inr assump_25 =>
              apply False.elim assump_25


variable (p0 p5 p6 p1 : Prop)
theorem file79_33695 : (((((False → False) ∨ (False ∨ p5)) ∧ ((p1 → False) → False)) ∧ (((False ∧ p5) ∧ (True → False)) ∧ ((p5 ∨ False) → (True → False)))) → ((((p0 ∧ True) ∨ (True ∧ p5)) → ((False ∨ p0) → (True ∨ p5))) ∧ (((p6 ∨ p5) ∧ (p5 → True)) → False))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    apply False.elim assump_4
  case inr assump_5 =>
    cases assump_2
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        cases assump_1
        case intro assump_18 assump_19 =>
          cases assump_18
          case intro assump_20 assump_21 =>
            cases assump_20
            case inl assump_22 =>
              cases assump_19
              case intro assump_28 assump_29 =>
                cases assump_28
                case intro assump_30 assump_31 =>
                  cases assump_30
                  case intro assump_32 assump_33 =>
                    apply False.elim assump_32
            case inr assump_23 =>
              cases assump_23
              case inl assump_36 =>
                apply False.elim assump_36
              case inr assump_37 =>
                cases assump_19
                case intro assump_44 assump_45 =>
                  cases assump_44
                  case intro assump_46 assump_47 =>
                    cases assump_46
                    case intro assump_48 assump_49 =>
                      apply False.elim assump_48
    case inr assump_11 =>
      cases assump_11
      case intro assump_52 assump_53 =>
        cases assump_1
        case intro assump_58 assump_59 =>
          cases assump_58
          case intro assump_60 assump_61 =>
            cases assump_60
            case inl assump_62 =>
              cases assump_59
              case intro assump_68 assump_69 =>
                cases assump_68
                case intro assump_70 assump_71 =>
                  cases assump_70
                  case intro assump_72 assump_73 =>
                    apply False.elim assump_72
            case inr assump_63 =>
              cases assump_63
              case inl assump_76 =>
                apply False.elim assump_76
              case inr assump_77 =>
                cases assump_59
                case intro assump_84 assump_85 =>
                  cases assump_84
                  case intro assump_86 assump_87 =>
                    cases assump_86
                    case intro assump_88 assump_89 =>
                      apply False.elim assump_88
  intro assump_92
  cases assump_92
  case intro assump_93 assump_94 =>
    cases assump_93
    case inl assump_95 =>
      cases assump_1
      case intro assump_101 assump_102 =>
        cases assump_101
        case intro assump_103 assump_104 =>
          cases assump_103
          case inl assump_105 =>
            cases assump_102
            case intro assump_111 assump_112 =>
              cases assump_111
              case intro assump_113 assump_114 =>
                cases assump_113
                case intro assump_115 assump_116 =>
                  apply False.elim assump_115
          case inr assump_106 =>
            cases assump_106
            case inl assump_119 =>
              apply False.elim assump_119
            case inr assump_120 =>
              cases assump_102
              case intro assump_127 assump_128 =>
                cases assump_127
                case intro assump_129 assump_130 =>
                  cases assump_129
                  case intro assump_131 assump_132 =>
                    apply False.elim assump_131
    case inr assump_96 =>
      cases assump_1
      case intro assump_139 assump_140 =>
        cases assump_139
        case intro assump_141 assump_142 =>
          cases assump_141
          case inl assump_143 =>
            cases assump_140
            case intro assump_149 assump_150 =>
              cases assump_149
              case intro assump_151 assump_152 =>
                cases assump_151
                case intro assump_153 assump_154 =>
                  apply False.elim assump_153
          case inr assump_144 =>
            cases assump_144
            case inl assump_157 =>
              apply False.elim assump_157
            case inr assump_158 =>
              cases assump_140
              case intro assump_165 assump_166 =>
                cases assump_165
                case intro assump_167 assump_168 =>
                  cases assump_167
                  case intro assump_169 assump_170 =>
                    apply False.elim assump_169


variable (p4 p6 p7 p1 p0 p5 : Prop)
theorem file79_38367 : (((((True ∨ p4) → False) ∧ ((p5 ∨ p0) → (p5 → True))) → (((p1 ∧ p7) → False) ∧ ((p7 → False) ∧ (p5 → p6)))) ∨ ((((p6 → False) ∨ (p7 ∨ False)) → False) → (((p4 ∨ p0) → False) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      have assump_50 : (True ∨ p4) := by
        apply Or.inl
        apply True.intro
      let assump_16 := assump_9 assump_50
      apply False.elim assump_16
  apply And.intro
  intro assump_20
  cases assump_1
  case intro assump_23 assump_24 =>
    have assump_51 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_30 := assump_23 assump_51
    apply False.elim assump_30
  intro assump_34
  cases assump_1
  case intro assump_37 assump_38 =>
    have assump_52 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_46 := assump_37 assump_52
    apply False.elim assump_46


variable (p0 p4 p2 p1 p3 p7 : Prop)
theorem file79_39420 : (((((p0 ∧ p4) → (p1 ∧ p2)) ∧ ((p3 → False) → (True → False))) ∧ (((p0 ∧ p3) ∧ (p2 ∧ False)) ∧ ((p0 ∧ p7) ∨ (True ∧ p3)))) → False) := by
  intro assump_13
  cases assump_13
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_15
      case intro assump_22 assump_23 =>
        cases assump_22
        case intro assump_24 assump_25 =>
          cases assump_24
          case intro assump_26 assump_27 =>
            cases assump_25
            case intro assump_32 assump_33 =>
              apply False.elim assump_33


variable (p7 p5 p2 p4 p3 p0 p1 : Prop)
theorem file79_40063 : (((((False → p5) ∨ (False → p3)) → ((False ∧ False) → (p7 ∨ True))) ∨ (((p5 ∨ p2) ∨ (p4 → False)) → False)) ∨ ((((p0 → False) ∨ (True → False)) → ((p1 → False) → (p3 → p1))) → (((p0 ∧ p1) ∧ (p0 → False)) ∨ ((True ∧ p3) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_21
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    apply False.elim assump_23


variable (p1 p6 : Prop)
theorem file79_40499 : (((((p1 → False) → False) → ((False → False) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((p1 → False) → False) → ((False → False) ∨ (p6 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p3 p4 p2 : Prop)
theorem file79_40891 : (((((p3 → p3) ∨ (p5 → p3)) → False) → False) ∨ ((((False → False) ∧ (p5 ∧ p2)) ∧ ((False → False) → False)) ∧ (((p3 ∧ p4) ∨ (False → p5)) ∧ ((p5 → p2) ∧ (False ∨ p2))))) := by
  apply Or.inl
  intro assump_1
  have assump_11 : ((p3 → p3) ∨ (p5 → p3)) := by
    apply Or.inl
    intro assump_5
    exact assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p5 p4 p1 p3 : Prop)
theorem file79_41322 : ((((((False ∧ True) → False) ∧ ((p1 → True) → (p4 → p4))) → False) ∧ ((((True ∧ p5) → False) → ((p3 ∨ p1) ∨ (True ∨ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_15 : (((True ∧ p5) → False) → ((p3 ∨ p1) ∨ (True ∨ p4))) := by
      intro assump_9
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_8 := assump_3 assump_15
    apply False.elim assump_8


variable (p3 p5 p4 p1 p7 p6 p0 : Prop)
theorem file79_41830 : (((((True → False) ∧ (p0 ∧ p0)) ∧ ((p7 ∨ p6) → (False → False))) → (((p1 ∨ p3) → False) → False)) ∨ ((((False ∨ p5) ∧ (p4 ∧ p0)) ∧ ((p0 → False) ∧ (p6 ∧ p7))) → (((p3 ∨ False) ∨ (p6 → False)) → ((p1 → False) ∨ (p7 → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_8
      case intro assump_11 assump_12 =>
        have assump_26 : True := by
          apply True.intro
        let assump_22 := assump_7 assump_26
        apply False.elim assump_22


variable (p2 p4 p5 p7 p1 p6 p3 p0 : Prop)
theorem file79_42484 : (((((p2 → False) → (p6 → False)) ∧ ((p1 → p6) → False)) ∧ (((p5 ∧ p2) ∨ (p4 ∨ p0)) → ((p1 ∨ True) ∧ (p6 ∧ p3)))) → ((((p2 ∧ p5) ∨ (p6 → True)) ∨ ((True → p6) ∨ (False → p0))) ∨ (((False → p4) → (p5 ∧ p5)) → ((p3 ∧ p7) → (True → False))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_12
      apply True.intro


variable (p2 p3 p6 p0 p5 p7 p1 : Prop)
theorem file79_43017 : ((((((p2 → p2) → (p5 ∨ p2)) ∧ ((p6 → p1) → False)) → (((p5 → False) ∧ (p1 → p2)) ∨ ((p7 ∨ p5) ∧ (p2 ∨ p3)))) ∧ ((((p5 ∧ p6) ∨ (p3 → p3)) → False) ∧ (((p2 ∧ p3) ∨ (p0 → p3)) ∧ ((False → False) → (p2 → False))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_10
        case inl assump_12 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            have assump_47 : (False → False) := by
              intro assump_23
              apply False.elim assump_23
            let assump_22 := assump_11 assump_47
            have assump_48 : p2 := by
              exact assump_14
            let assump_26 := assump_22 assump_48
            apply False.elim assump_26
        case inr assump_13 =>
          have assump_49 : ((p5 ∧ p6) ∨ (p3 → p3)) := by
            apply Or.inr
            intro assump_41
            exact assump_41
          let assump_40 := assump_6 assump_49
          apply False.elim assump_40


variable (p6 p3 p0 p7 p2 : Prop)
theorem file79_44186 : ((((((p3 ∧ True) ∨ (p2 ∨ p2)) ∨ ((False → False) → (False → False))) → False) ∧ ((((p0 ∧ p6) → False) → ((p7 → p7) ∨ (p0 ∧ p3))) → False)) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    have assump_22 : (((p0 ∧ p6) → False) → ((p7 → p7) ∨ (p0 ∧ p3))) := by
      intro assump_13
      apply Or.inl
      intro assump_16
      exact assump_16
    let assump_12 := assump_7 assump_22
    apply False.elim assump_12


variable (p2 p0 p5 p7 p1 : Prop)
theorem file79_44696 : ((((((True → False) → (p7 ∨ True)) → False) → (((True ∨ p1) → (True ∧ p5)) ∨ ((p0 ∨ p5) ∨ (p0 ∨ p2)))) → False) → False) := by
  intro assump_1
  have assump_33 : ((((True → False) → (p7 ∨ True)) → False) → (((True ∨ p1) → (True ∧ p5)) ∨ ((p0 ∨ p5) ∨ (p0 ∨ p2)))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply And.intro
    apply True.intro
    cases assump_8
    case inl assump_9 =>
      have assump_34 : ((True → False) → (p7 ∨ True)) := by
        intro assump_14
        apply Or.inr
        apply True.intro
      let assump_13 := assump_5 assump_34
      apply False.elim assump_13
    case inr assump_10 =>
      have assump_35 : ((True → False) → (p7 ∨ True)) := by
        intro assump_24
        apply Or.inr
        apply True.intro
      let assump_23 := assump_5 assump_35
      apply False.elim assump_23
  let assump_4 := assump_1 assump_33
  apply False.elim assump_4


variable (p4 p3 p5 p7 p2 p1 p6 : Prop)
theorem file79_45670 : (((((p7 → p6) → (p4 ∨ True)) ∧ ((p2 ∧ False) → False)) → False) → ((((p3 ∨ p5) → False) → ((p1 → p4) → False)) ∧ (((p3 → p3) → False) → ((False ∧ p1) ∧ (True → False))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  have assump_82 : (((p7 → p6) → (p4 ∨ True)) ∧ ((p2 ∧ False) → False)) := by
    apply And.intro
    intro assump_11
    apply Or.inr
    apply True.intro
    intro assump_14
    cases assump_14
    case intro assump_15 assump_16 =>
      apply False.elim assump_16
  let assump_10 := assump_1 assump_82
  apply False.elim assump_10
  intro assump_24
  apply And.intro
  apply And.intro
  have assump_83 : (((p7 → p6) → (p4 ∨ True)) ∧ ((p2 ∧ False) → False)) := by
    apply And.intro
    intro assump_30
    apply Or.inr
    apply True.intro
    intro assump_33
    cases assump_33
    case intro assump_34 assump_35 =>
      apply False.elim assump_35
  let assump_29 := assump_1 assump_83
  apply False.elim assump_29
  have assump_84 : (((p7 → p6) → (p4 ∨ True)) ∧ ((p2 ∧ False) → False)) := by
    apply And.intro
    intro assump_48
    apply Or.inr
    apply True.intro
    intro assump_51
    cases assump_51
    case intro assump_52 assump_53 =>
      apply False.elim assump_53
  let assump_47 := assump_1 assump_84
  apply False.elim assump_47
  intro assump_61
  have assump_85 : (((p7 → p6) → (p4 ∨ True)) ∧ ((p2 ∧ False) → False)) := by
    apply And.intro
    intro assump_69
    apply Or.inr
    apply True.intro
    intro assump_72
    cases assump_72
    case intro assump_73 assump_74 =>
      apply False.elim assump_74
  let assump_68 := assump_1 assump_85
  apply False.elim assump_68


variable (p6 p2 p5 p1 : Prop)
theorem file79_47378 : (((((p6 → False) ∧ (p2 ∨ p5)) → ((p5 ∨ p1) ∨ (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_40 : (((p6 → False) ∧ (p2 ∨ p5)) → ((p5 ∨ p1) ∨ (p1 → False))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case inl assump_10 =>
        apply Or.inr
        intro assump_14
        have assump_41 : (((p6 → False) ∧ (p2 ∨ p5)) → ((p5 ∨ p1) ∨ (p1 → False))) := by
          intro assump_21
          cases assump_21
          case intro assump_22 assump_23 =>
            cases assump_23
            case inl assump_26 =>
              apply Or.inl
              apply Or.inr
              exact assump_14
            case inr assump_27 =>
              apply Or.inl
              apply Or.inl
              exact assump_27
        let assump_20 := assump_1 assump_41
        apply False.elim assump_20
      case inr assump_11 =>
        apply Or.inl
        apply Or.inl
        exact assump_11
  let assump_4 := assump_1 assump_40
  apply False.elim assump_4


variable (p0 p3 p1 p5 p6 p4 : Prop)
theorem file79_48477 : (((((p3 ∧ p3) → (p1 → p1)) → ((p0 → p5) ∨ (p4 → False))) → False) → ((((False → p3) → False) → False) ∨ (((p6 → False) ∨ (p6 → p0)) ∨ ((p0 ∨ p4) ∨ (p6 ∧ p3))))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_14 : (False → p3) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_4 assump_14
  apply False.elim assump_7


variable (p5 p1 p3 : Prop)
theorem file79_48896 : (((((p3 ∧ p3) ∨ (p1 → p5)) → ((p1 → False) → (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_37 : (((p3 ∧ p3) ∨ (p1 → p5)) → ((p1 → False) → (p1 → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_5
    case inl assump_12 =>
      cases assump_12
      case intro assump_14 assump_15 =>
        have assump_38 : p1 := by
          exact assump_7
        let assump_22 := assump_6 assump_38
        apply False.elim assump_22
    case inr assump_13 =>
      have assump_39 : p1 := by
        exact assump_7
      let assump_30 := assump_6 assump_39
      apply False.elim assump_30
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p2 p1 p5 p3 : Prop)
theorem file79_49657 : (((((p1 ∨ p2) ∧ (p2 → p5)) ∧ ((True ∧ p2) → False)) ∧ (((p1 ∨ p5) ∧ (p3 ∧ p2)) ∧ ((p5 → p5) → (p1 → p3)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_16
            case intro assump_18 assump_19 =>
              cases assump_18
              case inl assump_20 =>
                cases assump_19
                case intro assump_24 assump_25 =>
                  have assump_125 : (True ∧ p2) := by
                    apply And.intro
                    apply True.intro
                    exact assump_25
                  let assump_41 := assump_5 assump_125
                  apply False.elim assump_41
              case inr assump_21 =>
                cases assump_19
                case intro assump_47 assump_48 =>
                  have assump_126 : (True ∧ p2) := by
                    apply And.intro
                    apply True.intro
                    exact assump_48
                  let assump_64 := assump_5 assump_126
                  apply False.elim assump_64
        case inr assump_9 =>
          cases assump_3
          case intro assump_74 assump_75 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_76
              case inl assump_78 =>
                cases assump_77
                case intro assump_82 assump_83 =>
                  have assump_127 : (True ∧ p2) := by
                    apply And.intro
                    apply True.intro
                    exact assump_83
                  let assump_99 := assump_5 assump_127
                  apply False.elim assump_99
              case inr assump_79 =>
                cases assump_77
                case intro assump_105 assump_106 =>
                  have assump_128 : (True ∧ p2) := by
                    apply And.intro
                    apply True.intro
                    exact assump_106
                  let assump_121 := assump_5 assump_128
                  apply False.elim assump_121


variable (p7 p5 p3 p1 p0 p4 p6 : Prop)
theorem file79_51980 : (((((p7 ∨ p0) ∨ (p4 ∧ p5)) → ((p7 ∨ True) → False)) ∧ (((p4 ∨ True) ∧ (p3 ∨ p6)) → ((p3 ∧ p7) ∨ (True → True)))) → ((((p1 ∧ p3) → (p5 → False)) → False) → (((False ∧ p7) → (p6 → p3)) ∨ ((p6 → True) ∨ (p4 ∧ p3))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    intro assump_11
    intro assump_12
    cases assump_11
    case intro assump_15 assump_16 =>
      apply False.elim assump_15


variable (p2 p3 p1 p5 p7 p6 p0 p4 : Prop)
theorem file79_52499 : (((((p3 → p4) ∨ (p0 → False)) ∧ ((p5 ∧ False) ∧ (p5 → False))) ∧ (((p7 → False) → False) ∧ ((p0 → p7) ∧ (p5 ∧ p7)))) → ((((p1 → p3) ∨ (p2 ∧ False)) ∧ ((p6 ∨ False) → (p0 → p6))) → False)) := by
  intro assump_5
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case inl assump_9 =>
      cases assump_5
      case intro assump_15 assump_16 =>
        cases assump_15
        case intro assump_17 assump_18 =>
          cases assump_17
          case inl assump_19 =>
            cases assump_18
            case intro assump_23 assump_24 =>
              cases assump_23
              case intro assump_25 assump_26 =>
                apply False.elim assump_26
          case inr assump_20 =>
            cases assump_18
            case intro assump_33 assump_34 =>
              cases assump_33
              case intro assump_35 assump_36 =>
                apply False.elim assump_36
    case inr assump_10 =>
      cases assump_10
      case intro assump_41 assump_42 =>
        apply False.elim assump_42


variable (p0 p3 p2 p5 p6 p4 p7 p1 : Prop)
theorem file79_53618 : (((((p3 → p1) ∨ (p1 → p0)) ∨ ((p6 ∧ p6) ∧ (p2 ∨ p6))) → (((p2 → False) → (p3 → True)) ∨ ((p0 ∨ p4) → False))) ∨ ((((p4 → p1) → False) ∧ ((p3 → False) → (p3 ∨ p1))) → (((p7 → p5) → False) → ((p2 ∧ p4) ∨ (p5 ∧ p4))))) := by
  apply Or.inl
  intro assump_9
  cases assump_9
  case inl assump_10 =>
    cases assump_10
    case inl assump_12 =>
      apply Or.inl
      intro assump_16
      intro assump_17
      apply True.intro
    case inr assump_13 =>
      apply Or.inl
      intro assump_20
      intro assump_21
      apply True.intro
  case inr assump_11 =>
    cases assump_11
    case intro assump_22 assump_23 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_23
        case inl assump_30 =>
          apply Or.inl
          intro assump_34
          intro assump_35
          apply True.intro
        case inr assump_31 =>
          apply Or.inl
          intro assump_38
          intro assump_39
          apply True.intro


variable (p3 p1 p4 p2 p0 p5 p7 : Prop)
theorem file79_54652 : (((((False → False) ∨ (p5 ∧ p4)) ∨ ((p5 → p4) ∨ (p1 ∧ False))) → (((p0 ∨ p7) ∨ (p4 → True)) → False)) → ((((p0 → False) ∨ (p4 ∧ True)) ∧ ((True → True) → False)) → (((p3 ∧ True) → False) → ((p3 ∨ p4) ∨ (False ∧ p2))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      have assump_35 : (((False → False) ∨ (p5 ∧ p4)) ∨ ((p5 → p4) ∨ (p1 ∧ False))) := by
        apply Or.inl
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
      let assump_16 := assump_1 assump_35
      have assump_36 : ((p0 ∨ p7) ∨ (p4 → True)) := by
        apply Or.inr
        intro assump_21
        apply True.intro
      let assump_20 := assump_16 assump_36
      apply False.elim assump_20
    case inr assump_9 =>
      cases assump_9
      case intro assump_25 assump_26 =>
        apply Or.inl
        apply Or.inr
        exact assump_25


variable (p6 p5 p2 p1 p3 p7 p4 : Prop)
theorem file79_55672 : (((((p7 → p4) ∨ (p2 ∨ p6)) → False) ∧ (((p4 → False) ∧ (False ∧ p5)) → False)) → ((((p4 ∨ True) ∧ (p3 ∧ p4)) ∧ ((p5 → False) ∨ (p4 ∧ p2))) → (((p3 ∨ p2) ∧ (p1 ∨ p6)) → ((p2 ∧ p7) ∨ (p1 ∨ p3))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_5
      case inl assump_10 =>
        cases assump_2
        case intro assump_14 assump_15 =>
          cases assump_14
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_17
              case intro assump_22 assump_23 =>
                cases assump_15
                case inl assump_28 =>
                  cases assump_1
                  case intro assump_32 assump_33 =>
                    apply Or.inr
                    apply Or.inl
                    exact assump_10
                case inr assump_29 =>
                  cases assump_29
                  case intro assump_38 assump_39 =>
                    cases assump_1
                    case intro assump_44 assump_45 =>
                      apply Or.inr
                      apply Or.inl
                      exact assump_10
            case inr assump_19 =>
              cases assump_17
              case intro assump_52 assump_53 =>
                cases assump_15
                case inl assump_58 =>
                  cases assump_1
                  case intro assump_62 assump_63 =>
                    apply Or.inr
                    apply Or.inl
                    exact assump_10
                case inr assump_59 =>
                  cases assump_59
                  case intro assump_68 assump_69 =>
                    cases assump_1
                    case intro assump_74 assump_75 =>
                      apply Or.inr
                      apply Or.inl
                      exact assump_10
      case inr assump_11 =>
        cases assump_2
        case intro assump_82 assump_83 =>
          cases assump_82
          case intro assump_84 assump_85 =>
            cases assump_84
            case inl assump_86 =>
              cases assump_85
              case intro assump_90 assump_91 =>
                cases assump_83
                case inl assump_96 =>
                  cases assump_1
                  case intro assump_100 assump_101 =>
                    apply Or.inr
                    apply Or.inr
                    exact assump_90
                case inr assump_97 =>
                  cases assump_97
                  case intro assump_106 assump_107 =>
                    cases assump_1
                    case intro assump_112 assump_113 =>
                      apply Or.inr
                      apply Or.inr
                      exact assump_90
            case inr assump_87 =>
              cases assump_85
              case intro assump_120 assump_121 =>
                cases assump_83
                case inl assump_126 =>
                  cases assump_1
                  case intro assump_130 assump_131 =>
                    apply Or.inr
                    apply Or.inr
                    exact assump_120
                case inr assump_127 =>
                  cases assump_127
                  case intro assump_136 assump_137 =>
                    cases assump_1
                    case intro assump_142 assump_143 =>
                      apply Or.inr
                      apply Or.inr
                      exact assump_120
    case inr assump_7 =>
      cases assump_5
      case inl assump_150 =>
        cases assump_2
        case intro assump_154 assump_155 =>
          cases assump_154
          case intro assump_156 assump_157 =>
            cases assump_156
            case inl assump_158 =>
              cases assump_157
              case intro assump_162 assump_163 =>
                cases assump_155
                case inl assump_168 =>
                  cases assump_1
                  case intro assump_172 assump_173 =>
                    apply Or.inr
                    apply Or.inl
                    exact assump_150
                case inr assump_169 =>
                  cases assump_169
                  case intro assump_178 assump_179 =>
                    cases assump_1
                    case intro assump_184 assump_185 =>
                      apply Or.inr
                      apply Or.inl
                      exact assump_150
            case inr assump_159 =>
              cases assump_157
              case intro assump_192 assump_193 =>
                cases assump_155
                case inl assump_198 =>
                  cases assump_1
                  case intro assump_202 assump_203 =>
                    apply Or.inr
                    apply Or.inl
                    exact assump_150
                case inr assump_199 =>
                  cases assump_199
                  case intro assump_208 assump_209 =>
                    cases assump_1
                    case intro assump_214 assump_215 =>
                      apply Or.inr
                      apply Or.inl
                      exact assump_150
      case inr assump_151 =>
        cases assump_2
        case intro assump_222 assump_223 =>
          cases assump_222
          case intro assump_224 assump_225 =>
            cases assump_224
            case inl assump_226 =>
              cases assump_225
              case intro assump_230 assump_231 =>
                cases assump_223
                case inl assump_236 =>
                  cases assump_1
                  case intro assump_240 assump_241 =>
                    apply Or.inr
                    apply Or.inr
                    exact assump_230
                case inr assump_237 =>
                  cases assump_237
                  case intro assump_246 assump_247 =>
                    cases assump_1
                    case intro assump_252 assump_253 =>
                      apply Or.inr
                      apply Or.inr
                      exact assump_230
            case inr assump_227 =>
              cases assump_225
              case intro assump_260 assump_261 =>
                cases assump_223
                case inl assump_266 =>
                  cases assump_1
                  case intro assump_270 assump_271 =>
                    apply Or.inr
                    apply Or.inr
                    exact assump_260
                case inr assump_267 =>
                  cases assump_267
                  case intro assump_276 assump_277 =>
                    cases assump_1
                    case intro assump_282 assump_283 =>
                      apply Or.inr
                      apply Or.inr
                      exact assump_260


variable (p4 p1 p7 p0 p6 p3 p5 : Prop)
theorem file79_62530 : ((((((p4 ∨ p5) → (p5 ∧ p0)) → False) → (((False → False) ∧ (p4 → False)) ∨ ((p3 → False) → (p1 ∨ False)))) ∧ ((((p7 → False) → (False ∧ p5)) → False) ∧ (((False → True) → (p6 → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_22 : ((False → True) → (p6 → p6)) := by
        intro assump_13
        intro assump_14
        exact assump_14
      let assump_12 := assump_7 assump_22
      apply False.elim assump_12


variable (p4 p3 p0 p1 p7 p6 p2 p5 : Prop)
theorem file79_63132 : (((((p1 → p4) → False) → ((p1 ∧ False) → False)) ∨ (((p4 → False) ∨ (p6 → False)) ∨ ((p5 ∧ True) ∧ (p4 → False)))) ∧ ((((p0 ∨ p6) → (False → False)) ∨ ((p0 ∨ p7) → False)) → (((p3 → True) ∨ (False → p2)) ∨ ((p2 ∧ p2) ∧ (True → False))))) := by
  apply And.intro
  apply Or.inl
  intro assump_26
  intro assump_27
  cases assump_27
  case intro assump_28 assump_29 =>
    apply False.elim assump_29
  intro assump_34
  cases assump_34
  case inl assump_35 =>
    apply Or.inl
    apply Or.inl
    intro assump_39
    apply True.intro
  case inr assump_36 =>
    apply Or.inl
    apply Or.inl
    intro assump_42
    apply True.intro


variable (p5 p2 p1 p4 p0 p6 p3 : Prop)
theorem file79_63827 : (((((p6 ∧ p5) ∨ (p4 → p1)) ∨ ((p4 ∨ False) → (p2 → False))) ∧ (((p3 ∨ p0) → (p6 ∨ p1)) ∧ ((False ∧ p3) ∧ (p5 → True)))) → ((((p3 → p4) → False) → False) ∧ (((p2 ∧ p4) → False) → False))) := by
  intro assump_29
  apply And.intro
  intro assump_30
  cases assump_29
  case intro assump_33 assump_34 =>
    cases assump_33
    case inl assump_35 =>
      cases assump_35
      case inl assump_37 =>
        cases assump_37
        case intro assump_39 assump_40 =>
          cases assump_34
          case intro assump_45 assump_46 =>
            cases assump_46
            case intro assump_49 assump_50 =>
              cases assump_49
              case intro assump_51 assump_52 =>
                apply False.elim assump_51
      case inr assump_38 =>
        cases assump_34
        case intro assump_57 assump_58 =>
          cases assump_58
          case intro assump_61 assump_62 =>
            cases assump_61
            case intro assump_63 assump_64 =>
              apply False.elim assump_63
    case inr assump_36 =>
      cases assump_34
      case intro assump_69 assump_70 =>
        cases assump_70
        case intro assump_73 assump_74 =>
          cases assump_73
          case intro assump_75 assump_76 =>
            apply False.elim assump_75
  intro assump_79
  cases assump_29
  case intro assump_82 assump_83 =>
    cases assump_82
    case inl assump_84 =>
      cases assump_84
      case inl assump_86 =>
        cases assump_86
        case intro assump_88 assump_89 =>
          cases assump_83
          case intro assump_94 assump_95 =>
            cases assump_95
            case intro assump_98 assump_99 =>
              cases assump_98
              case intro assump_100 assump_101 =>
                apply False.elim assump_100
      case inr assump_87 =>
        cases assump_83
        case intro assump_106 assump_107 =>
          cases assump_107
          case intro assump_110 assump_111 =>
            cases assump_110
            case intro assump_112 assump_113 =>
              apply False.elim assump_112
    case inr assump_85 =>
      cases assump_83
      case intro assump_118 assump_119 =>
        cases assump_119
        case intro assump_122 assump_123 =>
          cases assump_122
          case intro assump_124 assump_125 =>
            apply False.elim assump_124


variable (p4 p1 p2 p6 p0 p7 p5 : Prop)
theorem file79_66222 : (((((p5 → True) → False) ∧ ((False → False) → False)) ∨ (((p2 ∧ False) ∧ (False ∧ p6)) ∧ ((p0 → p1) ∨ (p4 ∧ p2)))) → ((((False → p1) → False) → ((p0 ∨ False) ∨ (False → False))) ∧ (((p1 ∧ p6) ∨ (p1 → False)) → ((p1 → False) ∧ (p5 → p7))))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      apply Or.inr
      intro assump_13
      apply False.elim assump_13
  case inr assump_6 =>
    cases assump_6
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        cases assump_18
        case intro assump_20 assump_21 =>
          apply False.elim assump_21
  intro assump_26
  apply And.intro
  intro assump_27
  cases assump_26
  case inl assump_30 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_1
      case inl assump_38 =>
        cases assump_38
        case intro assump_40 assump_41 =>
          have assump_153 : (False → False) := by
            intro assump_47
            apply False.elim assump_47
          let assump_46 := assump_41 assump_153
          apply False.elim assump_46
      case inr assump_39 =>
        cases assump_39
        case intro assump_53 assump_54 =>
          cases assump_53
          case intro assump_55 assump_56 =>
            cases assump_55
            case intro assump_57 assump_58 =>
              apply False.elim assump_58
  case inr assump_31 =>
    cases assump_1
    case inl assump_65 =>
      cases assump_65
      case intro assump_67 assump_68 =>
        have assump_154 : (False → False) := by
          intro assump_74
          apply False.elim assump_74
        let assump_73 := assump_68 assump_154
        apply False.elim assump_73
    case inr assump_66 =>
      cases assump_66
      case intro assump_80 assump_81 =>
        cases assump_80
        case intro assump_82 assump_83 =>
          cases assump_82
          case intro assump_84 assump_85 =>
            apply False.elim assump_85
  intro assump_90
  cases assump_26
  case inl assump_93 =>
    cases assump_93
    case intro assump_95 assump_96 =>
      cases assump_1
      case inl assump_101 =>
        cases assump_101
        case intro assump_103 assump_104 =>
          have assump_155 : (False → False) := by
            intro assump_110
            apply False.elim assump_110
          let assump_109 := assump_104 assump_155
          apply False.elim assump_109
      case inr assump_102 =>
        cases assump_102
        case intro assump_116 assump_117 =>
          cases assump_116
          case intro assump_118 assump_119 =>
            cases assump_118
            case intro assump_120 assump_121 =>
              apply False.elim assump_121
  case inr assump_94 =>
    cases assump_1
    case inl assump_128 =>
      cases assump_128
      case intro assump_130 assump_131 =>
        have assump_156 : (False → False) := by
          intro assump_137
          apply False.elim assump_137
        let assump_136 := assump_131 assump_156
        apply False.elim assump_136
    case inr assump_129 =>
      cases assump_129
      case intro assump_143 assump_144 =>
        cases assump_143
        case intro assump_145 assump_146 =>
          cases assump_145
          case intro assump_147 assump_148 =>
            apply False.elim assump_148


variable (p7 p6 p0 p1 p2 p3 : Prop)
theorem file79_69670 : (((((p1 ∧ p7) ∨ (p2 → p2)) ∨ ((p3 ∧ False) → (True → False))) ∨ (((p2 → False) → False) ∧ ((p3 ∧ p0) ∧ (p7 → p2)))) ∨ ((((False ∧ p2) → (False ∨ p2)) ∨ ((p2 → p6) → False)) → (((p7 → False) ∨ (p6 → p6)) → False))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  exact assump_1


variable (p4 p5 p1 p7 p6 p2 p3 : Prop)
theorem file79_70047 : (((((p2 ∧ p3) → False) ∨ ((p2 → False) ∧ (False → p3))) ∨ (((p7 → False) ∨ (p2 ∨ p7)) ∧ ((False ∧ p3) → (p1 ∧ p7)))) → ((((p4 → p2) ∨ (p6 ∨ p7)) ∧ ((p3 ∧ p7) → (p4 → False))) → (((True ∨ p1) → False) → ((p3 → p1) ∧ (p5 ∧ p7))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  intro assump_4
  cases assump_2
  case intro assump_9 assump_10 =>
    cases assump_9
    case inl assump_11 =>
      cases assump_1
      case inl assump_17 =>
        cases assump_17
        case inl assump_19 =>
          have assump_633 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_26 := assump_3 assump_633
          apply False.elim assump_26
        case inr assump_20 =>
          cases assump_20
          case intro assump_30 assump_31 =>
            have assump_634 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_40 := assump_3 assump_634
            apply False.elim assump_40
      case inr assump_18 =>
        cases assump_18
        case intro assump_44 assump_45 =>
          cases assump_44
          case inl assump_46 =>
            have assump_635 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_56 := assump_3 assump_635
            apply False.elim assump_56
          case inr assump_47 =>
            cases assump_47
            case inl assump_60 =>
              have assump_636 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_70 := assump_3 assump_636
              apply False.elim assump_70
            case inr assump_61 =>
              have assump_637 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_83 := assump_3 assump_637
              apply False.elim assump_83
    case inr assump_12 =>
      cases assump_12
      case inl assump_87 =>
        cases assump_1
        case inl assump_93 =>
          cases assump_93
          case inl assump_95 =>
            have assump_638 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_102 := assump_3 assump_638
            apply False.elim assump_102
          case inr assump_96 =>
            cases assump_96
            case intro assump_106 assump_107 =>
              have assump_639 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_116 := assump_3 assump_639
              apply False.elim assump_116
        case inr assump_94 =>
          cases assump_94
          case intro assump_120 assump_121 =>
            cases assump_120
            case inl assump_122 =>
              have assump_640 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_132 := assump_3 assump_640
              apply False.elim assump_132
            case inr assump_123 =>
              cases assump_123
              case inl assump_136 =>
                have assump_641 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_146 := assump_3 assump_641
                apply False.elim assump_146
              case inr assump_137 =>
                have assump_642 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_159 := assump_3 assump_642
                apply False.elim assump_159
      case inr assump_88 =>
        cases assump_1
        case inl assump_167 =>
          cases assump_167
          case inl assump_169 =>
            have assump_643 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_177 := assump_3 assump_643
            apply False.elim assump_177
          case inr assump_170 =>
            cases assump_170
            case intro assump_181 assump_182 =>
              have assump_644 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_192 := assump_3 assump_644
              apply False.elim assump_192
        case inr assump_168 =>
          cases assump_168
          case intro assump_196 assump_197 =>
            cases assump_196
            case inl assump_198 =>
              have assump_645 : p7 := by
                exact assump_88
              let assump_205 := assump_198 assump_645
              apply False.elim assump_205
            case inr assump_199 =>
              cases assump_199
              case inl assump_209 =>
                have assump_646 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_220 := assump_3 assump_646
                apply False.elim assump_220
              case inr assump_210 =>
                have assump_647 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_233 := assump_3 assump_647
                apply False.elim assump_233
  apply And.intro
  cases assump_2
  case intro assump_239 assump_240 =>
    cases assump_239
    case inl assump_241 =>
      cases assump_1
      case inl assump_247 =>
        cases assump_247
        case inl assump_249 =>
          have assump_648 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_256 := assump_3 assump_648
          apply False.elim assump_256
        case inr assump_250 =>
          cases assump_250
          case intro assump_260 assump_261 =>
            have assump_649 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_270 := assump_3 assump_649
            apply False.elim assump_270
      case inr assump_248 =>
        cases assump_248
        case intro assump_274 assump_275 =>
          cases assump_274
          case inl assump_276 =>
            have assump_650 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_286 := assump_3 assump_650
            apply False.elim assump_286
          case inr assump_277 =>
            cases assump_277
            case inl assump_290 =>
              have assump_651 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_300 := assump_3 assump_651
              apply False.elim assump_300
            case inr assump_291 =>
              have assump_652 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_312 := assump_3 assump_652
              apply False.elim assump_312
    case inr assump_242 =>
      cases assump_242
      case inl assump_316 =>
        cases assump_1
        case inl assump_322 =>
          cases assump_322
          case inl assump_324 =>
            have assump_653 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_331 := assump_3 assump_653
            apply False.elim assump_331
          case inr assump_325 =>
            cases assump_325
            case intro assump_335 assump_336 =>
              have assump_654 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_345 := assump_3 assump_654
              apply False.elim assump_345
        case inr assump_323 =>
          cases assump_323
          case intro assump_349 assump_350 =>
            cases assump_349
            case inl assump_351 =>
              have assump_655 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_361 := assump_3 assump_655
              apply False.elim assump_361
            case inr assump_352 =>
              cases assump_352
              case inl assump_365 =>
                have assump_656 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_375 := assump_3 assump_656
                apply False.elim assump_375
              case inr assump_366 =>
                have assump_657 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_387 := assump_3 assump_657
                apply False.elim assump_387
      case inr assump_317 =>
        cases assump_1
        case inl assump_395 =>
          cases assump_395
          case inl assump_397 =>
            have assump_658 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_404 := assump_3 assump_658
            apply False.elim assump_404
          case inr assump_398 =>
            cases assump_398
            case intro assump_408 assump_409 =>
              have assump_659 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_418 := assump_3 assump_659
              apply False.elim assump_418
        case inr assump_396 =>
          cases assump_396
          case intro assump_422 assump_423 =>
            cases assump_422
            case inl assump_424 =>
              have assump_660 : p7 := by
                exact assump_317
              let assump_431 := assump_424 assump_660
              apply False.elim assump_431
            case inr assump_425 =>
              cases assump_425
              case inl assump_435 =>
                have assump_661 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_445 := assump_3 assump_661
                apply False.elim assump_445
              case inr assump_436 =>
                have assump_662 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_457 := assump_3 assump_662
                apply False.elim assump_457
  cases assump_2
  case intro assump_463 assump_464 =>
    cases assump_463
    case inl assump_465 =>
      cases assump_1
      case inl assump_471 =>
        cases assump_471
        case inl assump_473 =>
          have assump_663 : (True ∨ p1) := by
            apply Or.inl
            apply True.intro
          let assump_480 := assump_3 assump_663
          apply False.elim assump_480
        case inr assump_474 =>
          cases assump_474
          case intro assump_484 assump_485 =>
            have assump_664 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_494 := assump_3 assump_664
            apply False.elim assump_494
      case inr assump_472 =>
        cases assump_472
        case intro assump_498 assump_499 =>
          cases assump_498
          case inl assump_500 =>
            have assump_665 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_510 := assump_3 assump_665
            apply False.elim assump_510
          case inr assump_501 =>
            cases assump_501
            case inl assump_514 =>
              have assump_666 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_524 := assump_3 assump_666
              apply False.elim assump_524
            case inr assump_515 =>
              exact assump_515
    case inr assump_466 =>
      cases assump_466
      case inl assump_532 =>
        cases assump_1
        case inl assump_538 =>
          cases assump_538
          case inl assump_540 =>
            have assump_667 : (True ∨ p1) := by
              apply Or.inl
              apply True.intro
            let assump_547 := assump_3 assump_667
            apply False.elim assump_547
          case inr assump_541 =>
            cases assump_541
            case intro assump_551 assump_552 =>
              have assump_668 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_561 := assump_3 assump_668
              apply False.elim assump_561
        case inr assump_539 =>
          cases assump_539
          case intro assump_565 assump_566 =>
            cases assump_565
            case inl assump_567 =>
              have assump_669 : (True ∨ p1) := by
                apply Or.inl
                apply True.intro
              let assump_577 := assump_3 assump_669
              apply False.elim assump_577
            case inr assump_568 =>
              cases assump_568
              case inl assump_581 =>
                have assump_670 : (True ∨ p1) := by
                  apply Or.inl
                  apply True.intro
                let assump_591 := assump_3 assump_670
                apply False.elim assump_591
              case inr assump_582 =>
                exact assump_582
      case inr assump_533 =>
        cases assump_1
        case inl assump_603 =>
          cases assump_603
          case inl assump_605 =>
            exact assump_533
          case inr assump_606 =>
            cases assump_606
            case intro assump_609 assump_610 =>
              exact assump_533
        case inr assump_604 =>
          cases assump_604
          case intro assump_615 assump_616 =>
            cases assump_615
            case inl assump_617 =>
              exact assump_533
            case inr assump_618 =>
              cases assump_618
              case inl assump_623 =>
                exact assump_533
              case inr assump_624 =>
                exact assump_624


variable (p0 p1 p4 : Prop)
theorem file79_83614 : (((((p4 → False) ∧ (p0 → False)) → ((p0 ∧ p1) → False)) → False) → False) := by
  intro assump_7
  have assump_32 : (((p4 → False) ∧ (p0 → False)) → ((p0 ∧ p1) → False)) := by
    intro assump_11
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_11
      case intro assump_19 assump_20 =>
        have assump_33 : p0 := by
          exact assump_13
        let assump_25 := assump_20 assump_33
        apply False.elim assump_25
  let assump_10 := assump_7 assump_32
  apply False.elim assump_10


variable (p6 p2 p5 p0 p1 p4 p7 : Prop)
theorem file79_84220 : ((((((p2 → False) ∨ (False ∧ p7)) ∨ ((p0 ∨ p6) ∨ (p1 ∧ p0))) ∧ (((False ∨ p2) ∧ (p0 → p5)) ∧ ((p7 ∧ p5) ∧ (p7 ∧ False)))) ∧ ((((p2 → False) → False) → ((p4 ∨ p2) → (p7 ∧ p5))) ∧ (((p7 ∨ p1) ∨ (p0 → p0)) → False))) → False) := by
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
              cases assump_14
              case inl assump_16 =>
                apply False.elim assump_16
              case inr assump_17 =>
                cases assump_13
                case intro assump_24 assump_25 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    cases assump_25
                    case intro assump_32 assump_33 =>
                      apply False.elim assump_33
        case inr assump_9 =>
          cases assump_9
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
      case inr assump_7 =>
        cases assump_7
        case inl assump_42 =>
          cases assump_42
          case inl assump_44 =>
            cases assump_5
            case intro assump_48 assump_49 =>
              cases assump_48
              case intro assump_50 assump_51 =>
                cases assump_50
                case inl assump_52 =>
                  apply False.elim assump_52
                case inr assump_53 =>
                  cases assump_49
                  case intro assump_60 assump_61 =>
                    cases assump_60
                    case intro assump_62 assump_63 =>
                      cases assump_61
                      case intro assump_68 assump_69 =>
                        apply False.elim assump_69
          case inr assump_45 =>
            cases assump_5
            case intro assump_76 assump_77 =>
              cases assump_76
              case intro assump_78 assump_79 =>
                cases assump_78
                case inl assump_80 =>
                  apply False.elim assump_80
                case inr assump_81 =>
                  cases assump_77
                  case intro assump_88 assump_89 =>
                    cases assump_88
                    case intro assump_90 assump_91 =>
                      cases assump_89
                      case intro assump_96 assump_97 =>
                        apply False.elim assump_97
        case inr assump_43 =>
          cases assump_43
          case intro assump_102 assump_103 =>
            cases assump_5
            case intro assump_108 assump_109 =>
              cases assump_108
              case intro assump_110 assump_111 =>
                cases assump_110
                case inl assump_112 =>
                  apply False.elim assump_112
                case inr assump_113 =>
                  cases assump_109
                  case intro assump_120 assump_121 =>
                    cases assump_120
                    case intro assump_122 assump_123 =>
                      cases assump_121
                      case intro assump_128 assump_129 =>
                        apply False.elim assump_129


variable (p2 p4 p3 p1 p6 p7 : Prop)
theorem file79_87630 : ((((((True → False) ∧ (p3 → p3)) ∨ ((True ∧ p1) ∨ (True ∨ p2))) → (((p7 → p1) → (p4 ∨ False)) ∨ ((p1 → False) → False))) ∧ ((((False → p4) ∨ (p6 ∧ p7)) → False) ∧ (((p3 ∧ True) → (False ∧ True)) ∧ ((p3 ∨ p3) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_25 : ((False → p4) ∨ (p6 ∧ p7)) := by
          apply Or.inl
          intro assump_19
          apply False.elim assump_19
        let assump_18 := assump_6 assump_25
        apply False.elim assump_18


variable (p1 p3 p5 p6 p0 p2 p4 : Prop)
theorem file79_88335 : (((((p5 ∧ p5) → (False ∧ p3)) → ((p0 → False) ∨ (p4 ∧ p5))) → (((p2 ∨ p5) ∧ (p0 ∧ p2)) → ((True → False) → (p2 → True)))) ∨ ((((p5 → False) → (p0 → p6)) → False) ∧ (((p4 ∨ p0) ∨ (False → True)) ∧ ((p4 ∧ p1) ∧ (p2 → False))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply True.intro


variable (p7 p3 p1 : Prop)
theorem file79_88720 : ((((((p3 ∨ p1) → (True ∧ False)) ∧ ((True ∨ p7) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((p3 ∨ p1) → (True ∧ False)) ∧ ((True ∨ p7) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_20 : (True ∨ p7) := by
        apply Or.inl
        apply True.intro
      let assump_12 := assump_7 assump_20
      apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p1 p6 p2 p3 p0 p7 p4 p5 : Prop)
theorem file79_89285 : (((((False ∧ p0) → False) → ((p4 ∧ p6) ∧ (p6 → False))) ∧ (((p0 → False) → False) → False)) → ((((p0 → p6) → (True ∨ p2)) ∧ ((p0 ∨ False) → False)) ∨ (((p7 → False) → (p1 ∨ p3)) → ((False ∧ False) ∧ (p5 → True))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    apply Or.inl
    apply And.intro
    intro assump_8
    apply Or.inl
    apply True.intro
    intro assump_11
    cases assump_11
    case inl assump_12 =>
      have assump_30 : ((p0 → False) → False) := by
        intro assump_18
        have assump_31 : p0 := by
          exact assump_12
        let assump_21 := assump_18 assump_31
        apply False.elim assump_21
      let assump_17 := assump_3 assump_30
      apply False.elim assump_17
    case inr assump_13 =>
      apply False.elim assump_13


variable (p3 p2 : Prop)
theorem file79_90132 : ((((((p2 → True) ∧ (True ∧ True)) ∧ ((False → p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p2 → True) ∧ (True ∧ True)) ∧ ((False → p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          have assump_31 : (False → p3) := by
            intro assump_21
            apply False.elim assump_21
          let assump_20 := assump_7 assump_31
          apply False.elim assump_20
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p5 p2 p6 : Prop)
theorem file79_90844 : ((((((p6 ∨ p2) → False) ∨ ((False → False) ∨ (p2 → False))) → False) ∧ ((((True ∨ p6) → False) → ((p5 ∧ p2) → (p2 ∧ p6))) → False)) → False) := by
  intro assump_7
  cases assump_7
  case intro assump_8 assump_9 =>
    have assump_40 : (((True ∨ p6) → False) → ((p5 ∧ p2) → (p2 ∧ p6))) := by
      intro assump_15
      intro assump_16
      apply And.intro
      cases assump_16
      case intro assump_17 assump_18 =>
        exact assump_18
      cases assump_16
      case intro assump_25 assump_26 =>
        have assump_41 : (True ∨ p6) := by
          apply Or.inl
          apply True.intro
        let assump_33 := assump_15 assump_41
        apply False.elim assump_33
    let assump_14 := assump_9 assump_40
    apply False.elim assump_14


variable (p0 p6 p7 : Prop)
theorem file79_91645 : (((((True ∨ p6) ∨ (p0 ∧ p7)) ∨ ((p6 → False) ∨ (p6 → False))) → False) → False) := by
  intro assump_1
  have assump_8 : (((True ∨ p6) ∨ (p0 ∧ p7)) ∨ ((p6 → False) ∨ (p6 → False))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p6 p7 p5 p4 : Prop)
theorem file79_92022 : (((((p4 ∨ p5) → False) → ((p6 → True) ∨ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_12 : (((p4 ∨ p5) → False) → ((p6 → True) ∨ (p7 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p3 p4 p1 p0 p2 p5 : Prop)
theorem file79_92400 : (((((p5 ∧ p5) ∧ (p4 → p4)) ∨ ((True → False) → (True → False))) ∨ (((True ∧ p1) ∨ (p2 ∧ True)) → ((p4 ∧ p6) ∧ (False ∨ p2)))) ∨ ((((p5 ∨ p4) → (p1 → False)) → False) ∨ (((p6 → False) → (p3 → False)) → ((p4 ∨ p0) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_1
  intro assump_2
  have assump_11 : True := by
    apply True.intro
  let assump_7 := assump_1 assump_11
  apply False.elim assump_7


variable (p5 p3 p7 p4 p6 p2 p0 p1 : Prop)
theorem file79_92891 : (((((True ∧ p1) ∨ (p3 ∧ p5)) → False) ∧ (((False ∧ p2) ∨ (True ∧ p3)) ∧ ((p0 → p3) → False))) → ((((p7 ∨ p4) ∧ (p5 → False)) ∨ ((False ∧ p5) → (False ∧ p4))) ∧ (((p5 → p0) → (True ∨ p3)) ∧ ((p3 → False) → (p6 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          apply False.elim assump_10
      case inr assump_9 =>
        cases assump_9
        case intro assump_14 assump_15 =>
          apply Or.inr
          intro assump_22
          apply And.intro
          cases assump_22
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
          cases assump_22
          case intro assump_27 assump_28 =>
            apply False.elim assump_27
  apply And.intro
  intro assump_31
  cases assump_1
  case intro assump_34 assump_35 =>
    cases assump_35
    case intro assump_38 assump_39 =>
      cases assump_38
      case inl assump_40 =>
        cases assump_40
        case intro assump_42 assump_43 =>
          apply False.elim assump_42
      case inr assump_41 =>
        cases assump_41
        case intro assump_46 assump_47 =>
          apply Or.inl
          apply True.intro
  intro assump_54
  intro assump_55
  cases assump_1
  case intro assump_60 assump_61 =>
    cases assump_61
    case intro assump_64 assump_65 =>
      cases assump_64
      case inl assump_66 =>
        cases assump_66
        case intro assump_68 assump_69 =>
          apply False.elim assump_68
      case inr assump_67 =>
        cases assump_67
        case intro assump_72 assump_73 =>
          have assump_87 : (p0 → p3) := by
            intro assump_81
            exact assump_73
          let assump_80 := assump_65 assump_87
          apply False.elim assump_80


variable (p2 p0 p6 p1 p4 p3 p5 : Prop)
theorem file79_94879 : (((((p6 ∨ False) ∨ (p0 ∨ True)) ∧ ((p1 → True) → (p2 → p2))) ∧ (((p2 ∧ p5) ∧ (p3 ∨ p5)) → ((p1 → False) → (True → p2)))) ∨ ((((p6 → False) → False) → ((p0 ∨ p4) → (True ∨ p4))) ∧ (((p1 ∧ p1) ∨ (True → p3)) ∧ ((p3 → False) → False)))) := by
  apply Or.inl
  apply And.intro
  apply And.intro
  apply Or.inr
  apply Or.inr
  apply True.intro
  intro assump_21
  intro assump_22
  exact assump_22
  intro assump_27
  intro assump_28
  intro assump_29
  cases assump_27
  case intro assump_34 assump_35 =>
    cases assump_34
    case intro assump_36 assump_37 =>
      cases assump_35
      case inl assump_42 =>
        exact assump_36
      case inr assump_43 =>
        exact assump_36


variable (p6 p3 p0 p5 p4 p2 p1 p7 : Prop)
theorem file79_95631 : (((((p4 → p2) ∨ (p1 → False)) ∨ ((p4 ∧ p2) ∧ (False ∧ p3))) ∨ (((p6 ∨ p3) → (True ∧ p4)) → ((p3 → False) ∧ (p7 ∨ p1)))) → ((((p5 → True) → False) ∨ ((p2 → False) ∧ (p4 ∧ p6))) → (((p0 ∧ p7) → (p0 ∨ p0)) ∨ ((p5 → False) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case inl assump_11 =>
          apply Or.inl
          intro assump_15
          cases assump_15
          case intro assump_16 assump_17 =>
            apply Or.inl
            exact assump_16
        case inr assump_12 =>
          apply Or.inl
          intro assump_24
          cases assump_24
          case intro assump_25 assump_26 =>
            apply Or.inl
            exact assump_25
      case inr assump_10 =>
        cases assump_10
        case intro assump_31 assump_32 =>
          cases assump_31
          case intro assump_33 assump_34 =>
            cases assump_32
            case intro assump_39 assump_40 =>
              apply False.elim assump_39
    case inr assump_8 =>
      apply Or.inl
      intro assump_45
      cases assump_45
      case intro assump_46 assump_47 =>
        apply Or.inl
        exact assump_46
  case inr assump_4 =>
    cases assump_4
    case intro assump_52 assump_53 =>
      cases assump_53
      case intro assump_56 assump_57 =>
        cases assump_1
        case inl assump_62 =>
          cases assump_62
          case inl assump_64 =>
            cases assump_64
            case inl assump_66 =>
              apply Or.inl
              intro assump_70
              cases assump_70
              case intro assump_71 assump_72 =>
                apply Or.inl
                exact assump_71
            case inr assump_67 =>
              apply Or.inl
              intro assump_79
              cases assump_79
              case intro assump_80 assump_81 =>
                apply Or.inl
                exact assump_80
          case inr assump_65 =>
            cases assump_65
            case intro assump_86 assump_87 =>
              cases assump_86
              case intro assump_88 assump_89 =>
                cases assump_87
                case intro assump_94 assump_95 =>
                  apply False.elim assump_94
        case inr assump_63 =>
          apply Or.inl
          intro assump_100
          cases assump_100
          case intro assump_101 assump_102 =>
            apply Or.inl
            exact assump_101


variable (p3 p7 p5 p6 p4 p0 p1 : Prop)
theorem file79_98235 : (((((p6 ∧ p3) ∧ (False ∧ p3)) → ((p6 ∧ p7) ∧ (p4 ∨ p0))) ∨ (((p7 → p1) → (p1 → False)) → ((p3 ∧ p6) → False))) ∨ ((((p5 ∨ p4) ∧ (p5 ∧ p4)) ∧ ((p5 → p0) → (False → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply And.intro
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        apply False.elim assump_10
  cases assump_1
  case intro assump_14 assump_15 =>
    cases assump_14
    case intro assump_16 assump_17 =>
      cases assump_15
      case intro assump_22 assump_23 =>
        apply False.elim assump_22
  cases assump_1
  case intro assump_26 assump_27 =>
    cases assump_26
    case intro assump_28 assump_29 =>
      cases assump_27
      case intro assump_34 assump_35 =>
        apply False.elim assump_34


variable (p3 p0 p2 p5 p7 : Prop)
theorem file79_99181 : ((((((p0 → p2) → False) → ((p5 → p7) ∧ (p3 ∨ p7))) → False) ∧ ((((False → False) → False) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_22 : (((False → False) → False) → False) := by
      intro assump_9
      have assump_23 : (False → False) := by
        intro assump_13
        apply False.elim assump_13
      let assump_12 := assump_9 assump_23
      apply False.elim assump_12
    let assump_8 := assump_3 assump_22
    apply False.elim assump_8


variable (p1 p6 p7 p3 p5 p4 : Prop)
theorem file79_99765 : (((((True → False) → False) → False) → (((p5 → False) → False) ∨ ((p1 → False) ∨ (p7 ∨ p1)))) ∨ ((((p7 → False) → (p3 → p1)) ∧ ((False ∧ p6) ∧ (p5 → False))) → (((p4 → p5) → False) → ((True ∨ p7) ∧ (False ∧ p1))))) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_19 : ((True → False) → False) := by
    intro assump_9
    have assump_20 : True := by
      apply True.intro
    let assump_12 := assump_9 assump_20
    apply False.elim assump_12
  let assump_8 := assump_1 assump_19
  apply False.elim assump_8


variable (p2 p5 p7 p1 p6 p4 p3 p0 : Prop)
theorem file79_100376 : ((((((p3 → p0) → (p2 ∧ p3)) → ((p4 ∧ True) ∨ (p7 → p7))) ∨ (((True ∨ p5) → False) ∨ ((p1 ∧ p2) ∨ (p1 ∧ p6)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p3 → p0) → (p2 ∧ p3)) → ((p4 ∧ True) ∨ (p7 → p7))) ∨ (((True ∨ p5) → False) ∨ ((p1 ∧ p2) ∨ (p1 ∧ p6)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inr
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p3 p6 p0 p2 p7 : Prop)
theorem file79_100873 : (((((p6 ∧ True) ∨ (p3 ∨ p0)) ∨ ((p0 → p2) ∨ (p7 → False))) → False) → False) := by
  intro assump_1
  have assump_16 : (((p6 ∧ True) ∨ (p3 ∨ p0)) ∨ ((p0 → p2) ∨ (p7 → False))) := by
    apply Or.inr
    apply Or.inl
    intro assump_5
    have assump_17 : (((p6 ∧ True) ∨ (p3 ∨ p0)) ∨ ((p0 → p2) ∨ (p7 → False))) := by
      apply Or.inl
      apply Or.inr
      apply Or.inr
      exact assump_5
    let assump_9 := assump_1 assump_17
    apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p4 p5 p3 p6 p2 p7 : Prop)
theorem file79_101467 : (((((True ∧ True) ∨ (p3 → False)) → ((p7 ∨ False) → (p1 → p7))) ∨ (((True ∨ False) → False) → False)) ∨ ((((p2 ∨ p2) ∨ (p5 ∧ p6)) ∧ ((p1 ∨ p3) → (p1 → False))) → (((p4 → False) → False) ∧ ((p3 → True) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_1
    case inl assump_10 =>
      cases assump_10
      case intro assump_12 assump_13 =>
        exact assump_6
    case inr assump_11 =>
      exact assump_6
  case inr assump_7 =>
    apply False.elim assump_7


variable (p4 p6 p0 p5 p7 p3 p1 : Prop)
theorem file79_102100 : (((((p0 → False) → False) → ((p3 ∧ p0) ∨ (p3 ∧ p6))) → False) → ((((p1 ∨ p0) → (p5 → False)) ∧ ((p7 ∨ p5) → (False → True))) → (((True ∨ p3) ∧ (p6 → p6)) ∨ ((p3 → False) ∨ (p4 → True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    apply And.intro
    apply Or.inl
    apply True.intro
    intro assump_11
    exact assump_11


variable (p3 p6 p1 p4 p7 p0 p5 : Prop)
theorem file79_102557 : ((((((p6 → p6) → False) → ((p1 ∧ p1) ∨ (p4 ∨ p3))) ∨ (((p0 → p6) ∧ (True ∧ p4)) ∧ ((p7 ∨ p6) → (p5 ∧ p1)))) ∧ ((((p4 → p3) ∧ (p3 → p5)) ∨ ((p5 ∧ p0) ∨ (p6 ∧ p6))) ∧ (((True ∧ p3) ∨ (p4 ∨ True)) → False))) → False) := by
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
          case intro assump_12 assump_13 =>
            have assump_106 : ((True ∧ p3) ∨ (p4 ∨ True)) := by
              apply Or.inr
              apply Or.inr
              apply True.intro
            let assump_20 := assump_9 assump_106
            apply False.elim assump_20
        case inr assump_11 =>
          cases assump_11
          case inl assump_24 =>
            cases assump_24
            case intro assump_26 assump_27 =>
              have assump_107 : ((True ∧ p3) ∨ (p4 ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_34 := assump_9 assump_107
              apply False.elim assump_34
          case inr assump_25 =>
            cases assump_25
            case intro assump_38 assump_39 =>
              have assump_108 : ((True ∧ p3) ∨ (p4 ∨ True)) := by
                apply Or.inr
                apply Or.inr
                apply True.intro
              let assump_46 := assump_9 assump_108
              apply False.elim assump_46
    case inr assump_5 =>
      cases assump_5
      case intro assump_50 assump_51 =>
        cases assump_50
        case intro assump_52 assump_53 =>
          cases assump_53
          case intro assump_56 assump_57 =>
            cases assump_3
            case intro assump_64 assump_65 =>
              cases assump_64
              case inl assump_66 =>
                cases assump_66
                case intro assump_68 assump_69 =>
                  have assump_109 : ((True ∧ p3) ∨ (p4 ∨ True)) := by
                    apply Or.inr
                    apply Or.inl
                    exact assump_57
                  let assump_76 := assump_65 assump_109
                  apply False.elim assump_76
              case inr assump_67 =>
                cases assump_67
                case inl assump_80 =>
                  cases assump_80
                  case intro assump_82 assump_83 =>
                    have assump_110 : ((True ∧ p3) ∨ (p4 ∨ True)) := by
                      apply Or.inr
                      apply Or.inl
                      exact assump_57
                    let assump_90 := assump_65 assump_110
                    apply False.elim assump_90
                case inr assump_81 =>
                  cases assump_81
                  case intro assump_94 assump_95 =>
                    have assump_111 : ((True ∧ p3) ∨ (p4 ∨ True)) := by
                      apply Or.inr
                      apply Or.inl
                      exact assump_57
                    let assump_102 := assump_65 assump_111
                    apply False.elim assump_102


variable (p3 p1 p0 p2 p7 p6 : Prop)
theorem file79_105738 : (((((p6 ∧ False) ∧ (p1 → False)) → False) → False) → ((((True → False) ∧ (p1 → False)) → ((p0 → p3) → (p2 → p7))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_20 : (((p6 ∧ False) ∧ (p1 → False)) → False) := by
    intro assump_8
    cases assump_8
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
  let assump_7 := assump_1 assump_20
  apply False.elim assump_7


variable (p6 p0 p4 : Prop)
theorem file79_106254 : ((((((False ∧ p4) → False) ∧ ((p0 → False) ∧ (p6 ∧ p0))) → False) → False) → False) := by
  intro assump_1
  have assump_29 : ((((False ∧ p4) → False) ∧ ((p0 → False) ∧ (p6 ∧ p0))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_30 : p0 := by
            exact assump_15
          let assump_22 := assump_10 assump_30
          apply False.elim assump_22
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4


variable (p1 p5 p2 p6 p4 p0 : Prop)
theorem file79_106924 : ((((((True ∧ True) → False) → ((p5 ∧ p2) ∧ (p1 ∧ p0))) → (((p4 → False) → False) → ((p6 ∧ p2) → (True ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((True ∧ True) → False) → ((p5 ∧ p2) ∧ (p1 ∧ p0))) → (((p4 → False) → False) → ((p6 ∧ p2) → (True ∨ False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p2 p6 p0 p3 p4 p1 : Prop)
theorem file79_107495 : ((((((p1 ∧ p0) → (p2 ∨ p3)) ∧ ((p2 → p6) → (p4 → False))) ∧ (((p3 → False) → False) ∧ ((p2 → p3) → False))) ∧ ((((True → False) → False) → False) ∧ (((p0 ∧ p0) ∧ (p0 → p3)) → False))) → False) := by
  intro assump_5
  cases assump_5
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_7
          case intro assump_22 assump_23 =>
            have assump_40 : ((True → False) → False) := by
              intro assump_30
              have assump_41 : True := by
                apply True.intro
              let assump_33 := assump_30 assump_41
              apply False.elim assump_33
            let assump_29 := assump_22 assump_40
            apply False.elim assump_29


variable (p6 p4 p7 p1 : Prop)
theorem file79_108411 : (((((False → True) ∧ (p7 ∨ p4)) ∧ ((p6 ∨ True) → (p7 → False))) ∨ (((p1 → p1) → False) → False)) ∨ ((((p7 → p4) → False) ∧ ((p1 ∧ False) → False)) → False)) := by
  apply Or.inl
  apply Or.inr
  intro assump_2
  have assump_12 : (p1 → p1) := by
    intro assump_6
    exact assump_6
  let assump_5 := assump_2 assump_12
  apply False.elim assump_5


variable (p5 p4 p3 p2 p1 p0 : Prop)
theorem file79_108819 : ((((((p4 → False) → False) ∨ ((p0 → False) → False)) → (((True ∧ True) → (p4 ∧ p2)) ∨ ((False → p1) → (p1 ∨ p5)))) ∧ ((((True ∧ p4) → False) ∧ ((False → False) ∧ (p4 ∧ p2))) ∨ (((p3 ∧ p0) ∨ (True ∨ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          cases assump_13
          case intro assump_16 assump_17 =>
            have assump_35 : (True ∧ p4) := by
              apply And.intro
              apply True.intro
              exact assump_16
            let assump_25 := assump_8 assump_35
            apply False.elim assump_25
    case inr assump_7 =>
      have assump_36 : ((p3 ∧ p0) ∨ (True ∨ p5)) := by
        apply Or.inr
        apply Or.inl
        apply True.intro
      let assump_31 := assump_7 assump_36
      apply False.elim assump_31


variable (p1 p5 p3 p4 p7 p2 : Prop)
theorem file79_109861 : ((((((p1 → False) ∨ (p4 → False)) → False) ∨ (((p4 ∨ False) ∨ (False → p2)) ∨ ((p5 → False) → (False ∨ p5)))) ∧ ((((p3 ∨ p7) → (p1 → False)) → ((True ∨ p2) ∧ (True ∨ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_66 : (((p3 ∨ p7) → (p1 → False)) → ((True ∨ p2) ∧ (True ∨ False))) := by
        intro assump_11
        apply And.intro
        apply Or.inl
        apply True.intro
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_66
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_19 =>
        cases assump_19
        case inl assump_21 =>
          cases assump_21
          case inl assump_23 =>
            have assump_67 : (((p3 ∨ p7) → (p1 → False)) → ((True ∨ p2) ∧ (True ∨ False))) := by
              intro assump_30
              apply And.intro
              apply Or.inl
              apply True.intro
              apply Or.inl
              apply True.intro
            let assump_29 := assump_3 assump_67
            apply False.elim assump_29
          case inr assump_24 =>
            apply False.elim assump_24
        case inr assump_22 =>
          have assump_68 : (((p3 ∨ p7) → (p1 → False)) → ((True ∨ p2) ∧ (True ∨ False))) := by
            intro assump_45
            apply And.intro
            apply Or.inl
            apply True.intro
            apply Or.inl
            apply True.intro
          let assump_44 := assump_3 assump_68
          apply False.elim assump_44
      case inr assump_20 =>
        have assump_69 : (((p3 ∨ p7) → (p1 → False)) → ((True ∨ p2) ∧ (True ∨ False))) := by
          intro assump_58
          apply And.intro
          apply Or.inl
          apply True.intro
          apply Or.inl
          apply True.intro
        let assump_57 := assump_3 assump_69
        apply False.elim assump_57


variable (p0 p1 p4 p6 p7 p2 p5 : Prop)
theorem file79_111883 : ((((((p6 ∧ p6) ∨ (p2 → p1)) → False) → False) ∧ ((((p2 → p0) ∧ (False ∧ p2)) ∧ ((False ∧ p5) → (p4 → p2))) ∧ (((p7 ∧ p1) ∨ (p5 → False)) → ((p4 ∨ p1) → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_11
          case intro assump_14 assump_15 =>
            apply False.elim assump_14


variable (p1 p0 p6 p4 p3 p5 p7 : Prop)
theorem file79_112479 : ((((((True → False) → (p3 ∧ p0)) ∨ ((p4 ∨ False) → (p1 ∨ False))) ∨ (((p0 ∧ p5) ∧ (p4 ∧ False)) → False)) ∧ ((((p7 → True) → False) ∧ ((p4 → p6) ∧ (True ∧ p7))) ∧ (((False ∨ p4) → False) ∧ ((p0 ∨ p5) → (p6 ∧ True))))) → False) := by
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
          case intro assump_12 assump_13 =>
            cases assump_13
            case intro assump_16 assump_17 =>
              cases assump_17
              case intro assump_20 assump_21 =>
                cases assump_11
                case intro assump_26 assump_27 =>
                  have assump_107 : (p7 → True) := by
                    intro assump_37
                    apply True.intro
                  let assump_36 := assump_12 assump_107
                  apply False.elim assump_36
      case inr assump_7 =>
        cases assump_3
        case intro assump_43 assump_44 =>
          cases assump_43
          case intro assump_45 assump_46 =>
            cases assump_46
            case intro assump_49 assump_50 =>
              cases assump_50
              case intro assump_53 assump_54 =>
                cases assump_44
                case intro assump_59 assump_60 =>
                  have assump_108 : (p7 → True) := by
                    intro assump_70
                    apply True.intro
                  let assump_69 := assump_45 assump_108
                  apply False.elim assump_69
    case inr assump_5 =>
      cases assump_3
      case intro assump_76 assump_77 =>
        cases assump_76
        case intro assump_78 assump_79 =>
          cases assump_79
          case intro assump_82 assump_83 =>
            cases assump_83
            case intro assump_86 assump_87 =>
              cases assump_77
              case intro assump_92 assump_93 =>
                have assump_109 : (p7 → True) := by
                  intro assump_103
                  apply True.intro
                let assump_102 := assump_78 assump_109
                apply False.elim assump_102


variable (p5 p3 p7 p2 p6 : Prop)
theorem file79_114745 : ((((((p2 → False) ∨ (p7 ∧ p3)) ∨ ((p5 ∨ False) ∨ (p7 → False))) → (((p6 ∨ True) → False) → False)) → False) → False) := by
  intro assump_5
  have assump_59 : ((((p2 → False) ∨ (p7 ∧ p3)) ∨ ((p5 ∨ False) ∨ (p7 → False))) → (((p6 ∨ True) → False) → False)) := by
    intro assump_9
    intro assump_10
    cases assump_9
    case inl assump_13 =>
      cases assump_13
      case inl assump_15 =>
        have assump_60 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_20 := assump_10 assump_60
        apply False.elim assump_20
      case inr assump_16 =>
        cases assump_16
        case intro assump_24 assump_25 =>
          have assump_61 : (p6 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_32 := assump_10 assump_61
          apply False.elim assump_32
    case inr assump_14 =>
      cases assump_14
      case inl assump_36 =>
        cases assump_36
        case inl assump_38 =>
          have assump_62 : (p6 ∨ True) := by
            apply Or.inr
            apply True.intro
          let assump_43 := assump_10 assump_62
          apply False.elim assump_43
        case inr assump_39 =>
          apply False.elim assump_39
      case inr assump_37 =>
        have assump_63 : (p6 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_52 := assump_10 assump_63
        apply False.elim assump_52
  let assump_8 := assump_5 assump_59
  apply False.elim assump_8


variable (p2 p3 p7 p0 p5 p6 p1 : Prop)
theorem file79_116300 : (((((p7 ∨ p5) → False) ∧ ((p6 → False) ∨ (p0 ∨ p3))) → (((p0 → p2) → (False → p0)) ∨ ((p7 ∨ p1) → (p2 → p7)))) ∨ ((((p0 → p0) → False) ∨ ((True → False) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      intro assump_10
      intro assump_11
      apply False.elim assump_11
    case inr assump_7 =>
      cases assump_7
      case inl assump_14 =>
        apply Or.inl
        intro assump_18
        intro assump_19
        apply False.elim assump_19
      case inr assump_15 =>
        apply Or.inl
        intro assump_24
        intro assump_25
        apply False.elim assump_25


variable (p3 p1 p7 p0 p5 p6 : Prop)
theorem file79_117072 : (((((p0 → True) ∧ (True → p3)) → ((p6 → False) → (True ∨ p5))) ∨ (((p0 ∧ p1) ∧ (p0 ∨ True)) ∧ ((False ∨ p7) → False))) ∨ ((((p3 ∨ p3) → (p3 → p1)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    apply Or.inl
    apply True.intro


variable (p1 p6 p0 p7 p2 p4 p3 : Prop)
theorem file79_117460 : ((((((p7 ∧ p0) ∧ (False → p0)) → ((p4 ∧ p1) → (p4 ∨ True))) ∨ (((p2 → p6) ∧ (p3 → False)) → ((p2 → False) → (p7 ∨ p3)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p7 ∧ p0) ∧ (False → p0)) → ((p4 ∧ p1) → (p4 ∨ True))) ∨ (((p2 → p6) ∧ (p3 → False)) → ((p2 → False) → (p7 ∨ p3)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_5
      case intro assump_13 assump_14 =>
        cases assump_13
        case intro assump_15 assump_16 =>
          apply Or.inl
          exact assump_7
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p2 p7 p6 p4 : Prop)
theorem file79_118170 : ((((((True → False) → False) → False) → (((p6 ∨ p2) → False) ∧ ((p4 → p2) ∧ (p7 ∨ True)))) → False) → False) := by
  intro assump_1
  have assump_60 : ((((True → False) → False) → False) → (((p6 ∨ p2) → False) ∧ ((p4 → p2) ∧ (p7 ∨ True)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_61 : ((True → False) → False) := by
        intro assump_14
        have assump_62 : True := by
          apply True.intro
        let assump_17 := assump_14 assump_62
        apply False.elim assump_17
      let assump_13 := assump_5 assump_61
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_63 : ((True → False) → False) := by
        intro assump_29
        have assump_64 : True := by
          apply True.intro
        let assump_32 := assump_29 assump_64
        apply False.elim assump_32
      let assump_28 := assump_5 assump_63
      apply False.elim assump_28
    apply And.intro
    intro assump_39
    have assump_65 : ((True → False) → False) := by
      intro assump_45
      have assump_66 : True := by
        apply True.intro
      let assump_48 := assump_45 assump_66
      apply False.elim assump_48
    let assump_44 := assump_5 assump_65
    apply False.elim assump_44
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_60
  apply False.elim assump_4


variable (p2 p4 p3 p0 p7 p6 p1 : Prop)
theorem file79_119621 : (((((p7 ∧ True) ∨ (p4 → p3)) → False) ∧ (((True → False) → (p0 ∨ p7)) ∨ ((False ∨ p6) ∧ (False ∨ p1)))) → ((((p7 ∧ p7) ∨ (p2 → True)) ∨ ((p7 ∨ p4) → False)) ∨ (((p6 ∧ p1) ∧ (True ∨ p0)) → False))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inr
      intro assump_10
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          apply False.elim assump_13
        case inr assump_14 =>
          cases assump_12
          case inl assump_19 =>
            apply False.elim assump_19
          case inr assump_20 =>
            apply Or.inl
            apply Or.inl
            apply Or.inr
            intro assump_25
            apply True.intro


variable (p1 p6 p7 p0 p4 p5 p2 : Prop)
theorem file79_120569 : ((((((p7 ∧ p4) → (p6 → False)) → False) ∧ (((p7 → False) → False) → ((p2 → p1) ∧ (p5 ∨ p1)))) ∧ ((((p0 → p4) → (p7 ∨ p7)) → ((True ∨ p6) ∨ (p7 ∧ p4))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_19 : (((p0 → p4) → (p7 ∨ p7)) → ((True ∨ p6) ∨ (p7 ∧ p4))) := by
        intro assump_13
        apply Or.inl
        apply Or.inl
        apply True.intro
      let assump_12 := assump_3 assump_19
      apply False.elim assump_12


variable (p7 p4 p3 p1 p5 p2 : Prop)
theorem file79_121177 : (((((True → False) → False) ∧ ((p1 ∧ p3) ∧ (False ∧ True))) → False) ∨ ((((p5 → False) ∨ (p4 ∨ True)) → False) ∨ (((p7 ∧ p2) → False) ∨ ((p7 → p7) → (False ∨ p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_7
        case intro assump_14 assump_15 =>
          apply False.elim assump_14


