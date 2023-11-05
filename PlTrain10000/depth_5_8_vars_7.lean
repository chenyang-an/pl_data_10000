variable (p3 p6 p2 p0 p7 p1 p4 p5 : Prop)
theorem file7_50 : (((((p1 ∧ p6) ∨ (p5 ∨ p6)) ∧ ((False ∧ p0) ∧ (p3 → False))) → False) ∨ ((((p3 ∧ False) ∧ (p2 → False)) ∨ ((p1 ∨ p5) ∨ (p4 → False))) ∨ (((p7 → False) → False) ∧ ((True ∨ p3) → (p4 → False))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_3
        case intro assump_12 assump_13 =>
          cases assump_12
          case intro assump_14 assump_15 =>
            apply False.elim assump_14
    case inr assump_5 =>
      cases assump_5
      case inl assump_18 =>
        cases assump_3
        case intro assump_22 assump_23 =>
          cases assump_22
          case intro assump_24 assump_25 =>
            apply False.elim assump_24
      case inr assump_19 =>
        cases assump_3
        case intro assump_30 assump_31 =>
          cases assump_30
          case intro assump_32 assump_33 =>
            apply False.elim assump_32


variable (p4 p3 p6 p2 p7 p5 p1 : Prop)
theorem file7_1122 : (((((p6 → False) ∧ (p5 → False)) ∨ ((p5 → True) ∨ (p4 → False))) → (((p3 → p3) ∨ (p1 ∧ p3)) ∨ ((p6 → False) ∧ (False → p2)))) ∨ ((((p7 → False) ∨ (p2 ∧ p4)) ∧ ((p5 ∧ p6) ∧ (p5 → True))) ∨ (((p3 ∧ True) → False) → ((True ∧ p2) ∨ (p1 ∧ p4))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      apply Or.inl
      apply Or.inl
      intro assump_10
      exact assump_10
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      apply Or.inl
      apply Or.inl
      intro assump_17
      exact assump_17
    case inr assump_14 =>
      apply Or.inl
      apply Or.inl
      intro assump_22
      exact assump_22


variable (p3 p0 p7 p5 p6 p4 p1 p2 : Prop)
theorem file7_1903 : (((((p5 → p4) → (p4 → False)) → ((p1 → True) ∧ (False ∨ p0))) → False) → ((((True → False) → (p6 → False)) ∨ ((False ∨ p2) → (p7 → p1))) ∨ (((p3 → False) ∧ (p4 → p3)) ∧ ((p3 → False) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  intro assump_5
  have assump_14 : True := by
    apply True.intro
  let assump_10 := assump_4 assump_14
  apply False.elim assump_10


variable (p3 p5 p1 p7 p4 p6 : Prop)
theorem file7_2363 : (((((p4 ∧ p5) ∨ (False ∨ p3)) ∧ ((p7 → p5) → (p7 ∨ p1))) ∧ (((p7 ∨ p3) → False) ∨ ((p6 ∨ p1) → False))) → ((((p4 → False) → (False → False)) → ((p3 ∨ p1) → (p3 → p1))) → (((False ∨ p7) → (p6 → True)) ∨ ((p4 → False) ∧ (p4 ∧ p1))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_6
          case inl assump_19 =>
            apply Or.inl
            intro assump_23
            intro assump_24
            apply True.intro
          case inr assump_20 =>
            apply Or.inl
            intro assump_27
            intro assump_28
            apply True.intro
      case inr assump_10 =>
        cases assump_10
        case inl assump_29 =>
          apply False.elim assump_29
        case inr assump_30 =>
          cases assump_6
          case inl assump_37 =>
            apply Or.inl
            intro assump_41
            intro assump_42
            apply True.intro
          case inr assump_38 =>
            apply Or.inl
            intro assump_45
            intro assump_46
            apply True.intro


variable (p4 p3 p6 p0 p1 p2 : Prop)
theorem file7_3681 : (((((True → False) → (p4 → p1)) ∨ ((p2 ∨ p6) → (p0 ∨ False))) → False) → ((((p2 ∨ p0) ∧ (p3 → False)) → ((p0 ∧ p0) ∧ (p4 → False))) → False)) := by
  intro assump_1
  intro assump_2
  have assump_21 : (((True → False) → (p4 → p1)) ∨ ((p2 ∨ p6) → (p0 ∨ False))) := by
    apply Or.inl
    intro assump_8
    intro assump_9
    have assump_22 : True := by
      apply True.intro
    let assump_14 := assump_8 assump_22
    apply False.elim assump_14
  let assump_7 := assump_1 assump_21
  apply False.elim assump_7


variable (p1 p2 p5 p6 p7 p0 p3 : Prop)
theorem file7_4257 : (((((p1 ∧ False) ∨ (True ∨ p5)) ∨ ((p2 ∨ p1) ∨ (p3 → False))) ∨ (((p7 ∧ p3) → False) → ((p2 → False) ∧ (p1 → p3)))) ∨ ((((p7 ∨ p6) → (p3 ∧ p0)) → False) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  apply Or.inl
  apply True.intro


variable (p7 p3 p2 p6 p5 p1 : Prop)
theorem file7_4580 : (((((p6 → False) ∧ (True ∧ False)) → ((p5 ∨ p2) ∨ (p3 → p2))) → (((True ∧ p3) → (p3 → False)) → ((p5 → True) ∨ (p5 → False)))) ∨ ((((p2 ∨ p1) ∨ (p7 → False)) → False) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply True.intro


variable (p5 p3 p1 p7 p0 p6 p2 p4 : Prop)
theorem file7_4929 : (((((p7 ∧ p5) → False) → False) ∧ (((True → False) → (p5 ∧ p5)) → False)) → ((((p0 → p2) ∨ (p3 → False)) ∧ ((p4 ∧ p1) ∨ (p7 → False))) → (((True → p2) → (p6 → False)) → False))) := by
  intro assump_5
  intro assump_6
  intro assump_7
  cases assump_6
  case intro assump_10 assump_11 =>
    cases assump_10
    case inl assump_12 =>
      cases assump_11
      case inl assump_16 =>
        cases assump_16
        case intro assump_18 assump_19 =>
          cases assump_5
          case intro assump_24 assump_25 =>
            have assump_130 : ((True → False) → (p5 ∧ p5)) := by
              intro assump_31
              apply And.intro
              have assump_131 : True := by
                apply True.intro
              let assump_34 := assump_31 assump_131
              apply False.elim assump_34
              have assump_132 : True := by
                apply True.intro
              let assump_40 := assump_31 assump_132
              apply False.elim assump_40
            let assump_30 := assump_25 assump_130
            apply False.elim assump_30
      case inr assump_17 =>
        cases assump_5
        case intro assump_49 assump_50 =>
          have assump_133 : ((True → False) → (p5 ∧ p5)) := by
            intro assump_56
            apply And.intro
            have assump_134 : True := by
              apply True.intro
            let assump_59 := assump_56 assump_134
            apply False.elim assump_59
            have assump_135 : True := by
              apply True.intro
            let assump_65 := assump_56 assump_135
            apply False.elim assump_65
          let assump_55 := assump_50 assump_133
          apply False.elim assump_55
    case inr assump_13 =>
      cases assump_11
      case inl assump_74 =>
        cases assump_74
        case intro assump_76 assump_77 =>
          cases assump_5
          case intro assump_82 assump_83 =>
            have assump_136 : ((True → False) → (p5 ∧ p5)) := by
              intro assump_89
              apply And.intro
              have assump_137 : True := by
                apply True.intro
              let assump_92 := assump_89 assump_137
              apply False.elim assump_92
              have assump_138 : True := by
                apply True.intro
              let assump_98 := assump_89 assump_138
              apply False.elim assump_98
            let assump_88 := assump_83 assump_136
            apply False.elim assump_88
      case inr assump_75 =>
        cases assump_5
        case intro assump_107 assump_108 =>
          have assump_139 : ((True → False) → (p5 ∧ p5)) := by
            intro assump_114
            apply And.intro
            have assump_140 : True := by
              apply True.intro
            let assump_117 := assump_114 assump_140
            apply False.elim assump_117
            have assump_141 : True := by
              apply True.intro
            let assump_123 := assump_114 assump_141
            apply False.elim assump_123
          let assump_113 := assump_108 assump_139
          apply False.elim assump_113


variable (p2 p4 p3 p6 p0 p5 p7 : Prop)
theorem file7_8076 : (((((p2 ∧ p7) ∨ (p7 ∧ p5)) ∧ ((p2 ∧ False) → (p6 → False))) → (((p6 → True) ∧ (p3 ∨ p5)) → ((True → p7) ∨ (True → False)))) ∨ ((((True ∧ p7) ∨ (False → p0)) ∨ ((p3 ∧ False) ∨ (False → False))) → (((True → p5) ∧ (p4 ∧ p2)) → ((p2 → False) ∨ (p6 ∨ p6))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply Or.inl
            intro assump_23
            exact assump_16
        case inr assump_14 =>
          cases assump_14
          case intro assump_26 assump_27 =>
            apply Or.inl
            intro assump_34
            exact assump_26
    case inr assump_8 =>
      cases assump_1
      case intro assump_39 assump_40 =>
        cases assump_39
        case inl assump_41 =>
          cases assump_41
          case intro assump_43 assump_44 =>
            apply Or.inl
            intro assump_51
            exact assump_44
        case inr assump_42 =>
          cases assump_42
          case intro assump_54 assump_55 =>
            apply Or.inl
            intro assump_62
            exact assump_54


variable (p6 p2 p3 p1 p0 p4 p5 p7 : Prop)
theorem file7_9465 : (((((p7 ∨ p4) → (p7 → False)) ∧ ((p2 → p4) ∧ (p5 → p0))) → (((p4 ∧ p3) ∨ (False ∧ p3)) ∨ ((p3 ∨ p1) ∨ (p7 → p6)))) ∨ ((((False ∨ True) ∨ (p7 → False)) ∧ ((p5 → False) → False)) ∧ (((p2 ∨ p1) ∧ (p5 ∧ False)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply Or.inr
      intro assump_12
      have assump_23 : (p7 ∨ p4) := by
        apply Or.inl
        exact assump_12
      let assump_18 := assump_2 assump_23
      have assump_24 : p7 := by
        exact assump_12
      let assump_19 := assump_18 assump_24
      apply False.elim assump_19


variable (p3 p7 p2 p6 p1 : Prop)
theorem file7_10202 : (((((False → False) → False) → False) ∨ (((p2 → False) → False) → False)) ∨ ((((p2 ∨ p7) → (p3 → False)) ∧ ((p3 → p1) ∧ (p6 ∨ True))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  have assump_11 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p0 p3 p6 p7 p4 p1 p2 : Prop)
theorem file7_10617 : ((((((p2 ∧ p4) → False) ∧ ((False → p3) ∧ (p2 → False))) ∧ (((p0 → p4) ∨ (p2 ∧ p1)) ∧ ((p3 ∧ False) ∧ (p3 ∨ p6)))) ∧ ((((p3 → False) → False) → ((p1 → p0) ∧ (p4 ∧ p6))) ∧ (((p2 ∨ p2) → False) → ((p7 → p4) ∧ (p7 ∨ p7))))) → False) := by
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          cases assump_10
          case intro assump_21 assump_22 =>
            cases assump_21
            case inl assump_23 =>
              cases assump_22
              case intro assump_27 assump_28 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  apply False.elim assump_30
            case inr assump_24 =>
              cases assump_24
              case intro assump_35 assump_36 =>
                cases assump_22
                case intro assump_41 assump_42 =>
                  cases assump_41
                  case intro assump_43 assump_44 =>
                    apply False.elim assump_44


variable (p3 p1 p4 p7 p6 p5 p2 : Prop)
theorem file7_11831 : ((((((p4 ∧ p1) ∧ (p4 → p2)) ∧ ((p3 → p4) ∧ (p7 ∧ p2))) → False) ∧ ((((p1 → False) ∨ (p7 ∧ p6)) ∨ ((p5 ∨ True) ∧ (p7 → False))) ∧ (((False ∧ p4) → (p2 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case inl assump_10 =>
          have assump_88 : ((False ∧ p4) → (p2 → False)) := by
            intro assump_17
            intro assump_18
            cases assump_17
            case intro assump_21 assump_22 =>
              apply False.elim assump_21
          let assump_16 := assump_7 assump_88
          apply False.elim assump_16
        case inr assump_11 =>
          cases assump_11
          case intro assump_28 assump_29 =>
            have assump_89 : ((False ∧ p4) → (p2 → False)) := by
              intro assump_37
              intro assump_38
              cases assump_37
              case intro assump_41 assump_42 =>
                apply False.elim assump_41
            let assump_36 := assump_7 assump_89
            apply False.elim assump_36
      case inr assump_9 =>
        cases assump_9
        case intro assump_48 assump_49 =>
          cases assump_48
          case inl assump_50 =>
            have assump_90 : ((False ∧ p4) → (p2 → False)) := by
              intro assump_59
              intro assump_60
              cases assump_59
              case intro assump_63 assump_64 =>
                apply False.elim assump_63
            let assump_58 := assump_7 assump_90
            apply False.elim assump_58
          case inr assump_51 =>
            have assump_91 : ((False ∧ p4) → (p2 → False)) := by
              intro assump_77
              intro assump_78
              cases assump_77
              case intro assump_81 assump_82 =>
                apply False.elim assump_81
            let assump_76 := assump_7 assump_91
            apply False.elim assump_76


variable (p1 p5 p3 p0 p7 p6 p2 : Prop)
theorem file7_13902 : (((((p3 → p0) ∧ (p0 ∧ p1)) → False) ∨ (((p5 → p3) ∧ (p2 → p1)) → False)) → ((((True ∨ p5) → False) → False) ∨ (((True ∨ p7) ∧ (True → p3)) → ((p6 → True) → (True → p2))))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    intro assump_6
    have assump_22 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_9 := assump_6 assump_22
    apply False.elim assump_9
  case inr assump_3 =>
    apply Or.inl
    intro assump_15
    have assump_23 : (True ∨ p5) := by
      apply Or.inl
      apply True.intro
    let assump_18 := assump_15 assump_23
    apply False.elim assump_18


variable (p3 p7 p5 p4 p2 p0 : Prop)
theorem file7_14596 : (((((p2 ∧ p3) ∨ (False → False)) ∧ ((p3 → p2) ∧ (p2 ∧ p5))) ∧ (((p0 ∨ p7) ∨ (p5 → p5)) → False)) → ((((p3 ∧ p3) ∧ (p4 → False)) → False) ∧ (((True ∨ False) ∨ (p2 ∨ False)) → ((p2 → False) → (False ∨ False))))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  cases assump_6
  case intro assump_7 assump_8 =>
    cases assump_7
    case intro assump_9 assump_10 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          cases assump_19
          case inl assump_21 =>
            cases assump_21
            case intro assump_23 assump_24 =>
              cases assump_20
              case intro assump_29 assump_30 =>
                cases assump_30
                case intro assump_33 assump_34 =>
                  have assump_191 : ((p0 ∨ p7) ∨ (p5 → p5)) := by
                    apply Or.inr
                    intro assump_42
                    exact assump_42
                  let assump_41 := assump_18 assump_191
                  apply False.elim assump_41
          case inr assump_22 =>
            cases assump_20
            case intro assump_50 assump_51 =>
              cases assump_51
              case intro assump_54 assump_55 =>
                have assump_192 : ((p0 ∨ p7) ∨ (p5 → p5)) := by
                  apply Or.inr
                  intro assump_63
                  exact assump_63
                let assump_62 := assump_18 assump_192
                apply False.elim assump_62
  intro assump_69
  intro assump_70
  cases assump_69
  case inl assump_73 =>
    cases assump_73
    case inl assump_75 =>
      cases assump_5
      case intro assump_79 assump_80 =>
        cases assump_79
        case intro assump_81 assump_82 =>
          cases assump_81
          case inl assump_83 =>
            cases assump_83
            case intro assump_85 assump_86 =>
              cases assump_82
              case intro assump_91 assump_92 =>
                cases assump_92
                case intro assump_95 assump_96 =>
                  have assump_193 : ((p0 ∨ p7) ∨ (p5 → p5)) := by
                    apply Or.inr
                    intro assump_104
                    exact assump_104
                  let assump_103 := assump_80 assump_193
                  apply False.elim assump_103
          case inr assump_84 =>
            cases assump_82
            case intro assump_112 assump_113 =>
              cases assump_113
              case intro assump_116 assump_117 =>
                have assump_194 : ((p0 ∨ p7) ∨ (p5 → p5)) := by
                  apply Or.inr
                  intro assump_125
                  exact assump_125
                let assump_124 := assump_80 assump_194
                apply False.elim assump_124
    case inr assump_76 =>
      apply False.elim assump_76
  case inr assump_74 =>
    cases assump_74
    case inl assump_133 =>
      cases assump_5
      case intro assump_137 assump_138 =>
        cases assump_137
        case intro assump_139 assump_140 =>
          cases assump_139
          case inl assump_141 =>
            cases assump_141
            case intro assump_143 assump_144 =>
              cases assump_140
              case intro assump_149 assump_150 =>
                cases assump_150
                case intro assump_153 assump_154 =>
                  have assump_195 : ((p0 ∨ p7) ∨ (p5 → p5)) := by
                    apply Or.inr
                    intro assump_162
                    exact assump_162
                  let assump_161 := assump_138 assump_195
                  apply False.elim assump_161
          case inr assump_142 =>
            cases assump_140
            case intro assump_170 assump_171 =>
              cases assump_171
              case intro assump_174 assump_175 =>
                have assump_196 : ((p0 ∨ p7) ∨ (p5 → p5)) := by
                  apply Or.inr
                  intro assump_183
                  exact assump_183
                let assump_182 := assump_138 assump_196
                apply False.elim assump_182
    case inr assump_134 =>
      apply False.elim assump_134


variable (p6 p0 p3 p1 p7 p5 : Prop)
theorem file7_18797 : ((((((p6 ∧ p5) ∧ (p0 ∨ True)) → ((p6 → p7) → (p3 → True))) ∨ (((p1 → p1) → (p3 → p5)) → False)) → False) → False) := by
  intro assump_26
  have assump_36 : ((((p6 ∧ p5) ∧ (p0 ∨ True)) → ((p6 → p7) → (p3 → True))) ∨ (((p1 → p1) → (p3 → p5)) → False)) := by
    apply Or.inl
    intro assump_30
    intro assump_31
    intro assump_32
    apply True.intro
  let assump_29 := assump_26 assump_36
  apply False.elim assump_29


variable (p5 p3 p1 p0 p6 p4 : Prop)
theorem file7_19280 : (((((p4 ∨ p3) ∧ (True → False)) ∧ ((p0 ∨ p6) → (False → False))) → False) ∧ ((((p1 ∨ True) ∨ (p5 → False)) → False) → False)) := by
  apply And.intro
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        have assump_37 : True := by
          apply True.intro
        let assump_15 := assump_5 assump_37
        apply False.elim assump_15
      case inr assump_7 =>
        have assump_38 : True := by
          apply True.intro
        let assump_26 := assump_5 assump_38
        apply False.elim assump_26
  intro assump_30
  have assump_39 : ((p1 ∨ True) ∨ (p5 → False)) := by
    apply Or.inl
    apply Or.inr
    apply True.intro
  let assump_33 := assump_30 assump_39
  apply False.elim assump_33


variable (p2 p6 p7 p3 p0 p4 p1 : Prop)
theorem file7_20170 : (((((True ∨ False) → False) ∨ ((p2 ∧ p6) ∧ (p4 → False))) ∨ (((p3 → False) ∧ (p0 → False)) → ((p1 → p1) → False))) → ((((False ∨ p2) → (p6 ∧ True)) → ((True → False) ∧ (p7 ∨ p7))) → (((False → True) ∧ (p4 ∨ True)) ∨ ((p0 → False) → (False ∨ p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case inl assump_5 =>
    cases assump_5
    case inl assump_7 =>
      apply Or.inl
      apply And.intro
      intro assump_11
      apply True.intro
      apply Or.inr
      apply True.intro
    case inr assump_8 =>
      cases assump_8
      case intro assump_12 assump_13 =>
        cases assump_12
        case intro assump_14 assump_15 =>
          apply Or.inl
          apply And.intro
          intro assump_22
          apply True.intro
          apply Or.inr
          apply True.intro
  case inr assump_6 =>
    apply Or.inl
    apply And.intro
    intro assump_25
    apply True.intro
    apply Or.inr
    apply True.intro


variable (p4 p7 p0 p1 p5 : Prop)
theorem file7_21171 : (((((True → p5) ∧ (True → p1)) → ((False ∧ p4) → False)) → False) → ((((p5 ∧ p4) → False) → False) ∧ (((p1 → False) → (p0 → False)) → ((p7 → False) → False)))) := by
  intro assump_5
  apply And.intro
  intro assump_6
  have assump_39 : (((True → p5) ∧ (True → p1)) → ((False ∧ p4) → False)) := by
    intro assump_12
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      apply False.elim assump_14
  let assump_11 := assump_5 assump_39
  apply False.elim assump_11
  intro assump_21
  intro assump_22
  have assump_40 : (((True → p5) ∧ (True → p1)) → ((False ∧ p4) → False)) := by
    intro assump_30
    intro assump_31
    cases assump_31
    case intro assump_32 assump_33 =>
      apply False.elim assump_32
  let assump_29 := assump_5 assump_40
  apply False.elim assump_29


variable (p6 p7 : Prop)
theorem file7_22029 : ((((((True ∨ p6) ∨ (p7 ∧ True)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_15 : ((((True ∨ p6) ∨ (p7 ∧ True)) → False) → False) := by
    intro assump_5
    have assump_16 : ((True ∨ p6) ∨ (p7 ∧ True)) := by
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_8 := assump_5 assump_16
    apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p3 p2 p7 p0 p6 p5 p4 : Prop)
theorem file7_22525 : (((((p7 ∨ False) → False) → ((p7 → False) ∨ (p6 ∧ p6))) → (((p6 → p2) → False) ∧ ((p7 ∧ p3) ∧ (p7 → True)))) → ((((p3 ∧ False) → (p3 ∧ p5)) ∨ ((p0 ∨ p4) ∨ (p5 → False))) ∨ (((p5 → p6) ∨ (p4 ∧ p0)) → False))) := by
  intro assump_24
  apply Or.inl
  apply Or.inl
  intro assump_27
  apply And.intro
  cases assump_27
  case intro assump_28 assump_29 =>
    apply False.elim assump_29
  cases assump_27
  case intro assump_34 assump_35 =>
    apply False.elim assump_35


variable (p5 p0 p6 p2 p1 p7 p3 : Prop)
theorem file7_23056 : (((((False → False) → False) ∨ ((p6 ∧ p1) ∧ (p6 → False))) → (((p6 ∧ p6) → (p0 ∨ p0)) ∨ ((p5 → True) ∧ (p6 → False)))) ∨ ((((p2 → p0) ∧ (True ∧ p5)) ∧ ((p3 → p6) ∧ (p3 ∨ True))) → (((p5 ∨ False) → False) → ((p7 ∨ p6) → (True ∧ p3))))) := by
  apply Or.inl
  intro assump_5
  cases assump_5
  case inl assump_6 =>
    apply Or.inl
    intro assump_10
    cases assump_10
    case intro assump_11 assump_12 =>
      have assump_49 : (False → False) := by
        intro assump_20
        apply False.elim assump_20
      let assump_19 := assump_6 assump_49
      apply False.elim assump_19
  case inr assump_7 =>
    cases assump_7
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        apply Or.inl
        intro assump_36
        cases assump_36
        case intro assump_37 assump_38 =>
          have assump_50 : p6 := by
            exact assump_38
          let assump_45 := assump_27 assump_50
          apply False.elim assump_45


variable (p4 p1 p5 p2 p6 p7 p3 : Prop)
theorem file7_24107 : ((((((p3 ∧ p1) ∨ (p2 ∨ p6)) ∧ ((p6 ∧ p2) → False)) → (((p2 → False) ∨ (p7 → False)) → False)) ∧ ((((p2 → p4) ∨ (p6 → False)) → False) ∧ (((p5 → False) → (p5 → p6)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      have assump_26 : ((p5 → False) → (p5 → p6)) := by
        intro assump_13
        intro assump_14
        have assump_27 : p5 := by
          exact assump_14
        let assump_19 := assump_13 assump_27
        apply False.elim assump_19
      let assump_12 := assump_7 assump_26
      apply False.elim assump_12


variable (p4 p7 p0 p3 p5 : Prop)
theorem file7_24796 : ((((((p3 ∨ p3) ∨ (True ∨ p7)) → ((False ∧ p4) ∧ (p5 ∧ p0))) → (((p3 ∧ p5) → (True → True)) ∨ ((p7 → False) → False))) → ((((p4 ∨ p3) ∧ (True → False)) → False) → False)) → False) := by
  intro assump_1
  have assump_35 : ((((p3 ∨ p3) ∨ (True ∨ p7)) → ((False ∧ p4) ∧ (p5 ∧ p0))) → (((p3 ∧ p5) → (True → True)) ∨ ((p7 → False) → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    intro assump_9
    apply True.intro
  let assump_4 := assump_1 assump_35
  have assump_36 : (((p4 ∨ p3) ∧ (True → False)) → False) := by
    intro assump_11
    cases assump_11
    case intro assump_12 assump_13 =>
      cases assump_12
      case inl assump_14 =>
        have assump_37 : True := by
          apply True.intro
        let assump_20 := assump_13 assump_37
        apply False.elim assump_20
      case inr assump_15 =>
        have assump_38 : True := by
          apply True.intro
        let assump_28 := assump_13 assump_38
        apply False.elim assump_28
  let assump_10 := assump_4 assump_36
  apply False.elim assump_10


variable (p0 p7 p1 : Prop)
theorem file7_25895 : (((((True → p1) → False) → ((p7 → p7) ∨ (p0 → False))) → False) → False) := by
  intro assump_1
  have assump_14 : (((True → p1) → False) → ((p7 → p7) ∨ (p0 → False))) := by
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p0 p6 p7 p3 p5 p4 : Prop)
theorem file7_26271 : (((((p0 → False) → (p4 ∧ p0)) → ((p6 ∨ p0) ∧ (True ∧ p7))) ∧ (((p1 ∧ False) ∨ (p5 ∨ p5)) → ((True ∨ p0) → (p7 ∧ False)))) → ((((True → p7) → (p0 → p0)) ∨ ((p6 → p6) ∧ (p0 → False))) ∨ (((p3 ∧ p7) ∧ (p1 → p4)) ∨ ((False ∧ True) ∧ (False → p7))))) := by
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    apply Or.inl
    apply Or.inl
    intro assump_18
    intro assump_19
    exact assump_19


variable (p1 p5 : Prop)
theorem file7_26737 : (((((False → False) → False) → ((p1 ∨ p5) → False)) → False) → False) := by
  intro assump_1
  have assump_34 : (((False → False) → False) → ((p1 ∨ p5) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      have assump_35 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_5 assump_35
      apply False.elim assump_13
    case inr assump_8 =>
      have assump_36 : (False → False) := by
        intro assump_25
        apply False.elim assump_25
      let assump_24 := assump_5 assump_36
      apply False.elim assump_24
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p7 p4 p1 p2 p3 p6 p5 p0 : Prop)
theorem file7_27501 : ((((((False ∧ p2) ∨ (p7 → True)) ∧ ((p4 ∨ p7) → (True ∨ p6))) → (((p1 → p6) → False) → ((True ∨ p0) → False))) ∧ ((((p0 ∧ p0) → (p0 ∧ p7)) → ((p6 ∨ False) ∧ (p3 ∨ p4))) ∧ (((p0 ∨ p0) ∨ (p5 ∨ p5)) ∧ ((p2 → False) ∧ (True ∧ False))))) → False) := by
  intro assump_42
  cases assump_42
  case intro assump_43 assump_44 =>
    cases assump_44
    case intro assump_47 assump_48 =>
      cases assump_48
      case intro assump_51 assump_52 =>
        cases assump_51
        case inl assump_53 =>
          cases assump_53
          case inl assump_55 =>
            cases assump_52
            case intro assump_59 assump_60 =>
              cases assump_60
              case intro assump_63 assump_64 =>
                apply False.elim assump_64
          case inr assump_56 =>
            cases assump_52
            case intro assump_71 assump_72 =>
              cases assump_72
              case intro assump_75 assump_76 =>
                apply False.elim assump_76
        case inr assump_54 =>
          cases assump_54
          case inl assump_81 =>
            cases assump_52
            case intro assump_85 assump_86 =>
              cases assump_86
              case intro assump_89 assump_90 =>
                apply False.elim assump_90
          case inr assump_82 =>
            cases assump_52
            case intro assump_97 assump_98 =>
              cases assump_98
              case intro assump_101 assump_102 =>
                apply False.elim assump_102


variable (p3 p6 p0 p2 p7 p5 p1 p4 : Prop)
theorem file7_29054 : ((((((p4 → False) → (p0 ∨ p6)) ∨ ((False ∨ p6) ∨ (p5 ∨ True))) → (((True ∨ False) ∨ (p6 → p0)) ∧ ((p2 ∨ True) ∨ (False → p2)))) → ((((p4 ∧ p4) ∨ (p3 → p1)) ∧ ((True ∨ p7) → False)) ∨ (((False ∨ p1) → False) ∧ ((True ∧ False) ∧ (p0 ∧ p3))))) → False) := by
  intro assump_1
  have assump_81 : ((((p4 → False) → (p0 ∨ p6)) ∨ ((False ∨ p6) ∨ (p5 ∨ True))) → (((True ∨ False) ∨ (p6 → p0)) ∧ ((p2 ∨ True) ∨ (False → p2)))) := by
    intro assump_5
    apply And.intro
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply False.elim assump_12
        case inr assump_13 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
      case inr assump_11 =>
        cases assump_11
        case inl assump_18 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
        case inr assump_19 =>
          apply Or.inl
          apply Or.inl
          apply True.intro
    cases assump_5
    case inl assump_24 =>
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_25 =>
      cases assump_25
      case inl assump_28 =>
        cases assump_28
        case inl assump_30 =>
          apply False.elim assump_30
        case inr assump_31 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
      case inr assump_29 =>
        cases assump_29
        case inl assump_36 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
        case inr assump_37 =>
          apply Or.inl
          apply Or.inr
          apply True.intro
  let assump_4 := assump_1 assump_81
  cases assump_4
  case inl assump_43 =>
    cases assump_43
    case intro assump_45 assump_46 =>
      cases assump_45
      case inl assump_47 =>
        cases assump_47
        case intro assump_49 assump_50 =>
          have assump_82 : (True ∨ p7) := by
            apply Or.inl
            apply True.intro
          let assump_57 := assump_46 assump_82
          apply False.elim assump_57
      case inr assump_48 =>
        have assump_83 : (True ∨ p7) := by
          apply Or.inl
          apply True.intro
        let assump_65 := assump_46 assump_83
        apply False.elim assump_65
  case inr assump_44 =>
    cases assump_44
    case intro assump_69 assump_70 =>
      cases assump_70
      case intro assump_73 assump_74 =>
        cases assump_73
        case intro assump_75 assump_76 =>
          apply False.elim assump_76


variable (p7 p3 p5 p6 p1 p4 p2 p0 : Prop)
theorem file7_31731 : (((((p7 ∧ p3) ∧ (True ∧ p0)) ∧ ((False → True) → False)) → (((False → p4) → (p4 ∧ p0)) ∧ ((p6 → False) ∧ (p2 → False)))) ∨ ((((p5 ∨ False) ∧ (p2 ∧ p3)) → ((p4 → False) ∧ (p1 ∨ p5))) ∧ (((p7 ∨ p1) → (p6 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  apply And.intro
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case intro assump_15 assump_16 =>
          have assump_100 : (False → True) := by
            intro assump_24
            apply True.intro
          let assump_23 := assump_6 assump_100
          apply False.elim assump_23
  cases assump_1
  case intro assump_30 assump_31 =>
    cases assump_30
    case intro assump_32 assump_33 =>
      cases assump_32
      case intro assump_34 assump_35 =>
        cases assump_33
        case intro assump_40 assump_41 =>
          exact assump_41
  apply And.intro
  intro assump_48
  cases assump_1
  case intro assump_51 assump_52 =>
    cases assump_51
    case intro assump_53 assump_54 =>
      cases assump_53
      case intro assump_55 assump_56 =>
        cases assump_54
        case intro assump_61 assump_62 =>
          have assump_101 : (False → True) := by
            intro assump_70
            apply True.intro
          let assump_69 := assump_52 assump_101
          apply False.elim assump_69
  intro assump_74
  cases assump_1
  case intro assump_77 assump_78 =>
    cases assump_77
    case intro assump_79 assump_80 =>
      cases assump_79
      case intro assump_81 assump_82 =>
        cases assump_80
        case intro assump_87 assump_88 =>
          have assump_102 : (False → True) := by
            intro assump_96
            apply True.intro
          let assump_95 := assump_78 assump_102
          apply False.elim assump_95


variable (p6 p4 p0 p7 p3 p5 p2 : Prop)
theorem file7_33705 : ((((((p3 → False) ∧ (p3 ∧ p5)) → ((p0 ∨ p6) ∨ (p2 ∧ p6))) ∨ (((p3 → False) ∨ (p4 ∧ p7)) ∧ ((p4 → False) → (p0 ∨ p4)))) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p3 → False) ∧ (p3 ∧ p5)) → ((p0 ∨ p6) ∨ (p2 ∧ p6))) ∨ (((p3 → False) ∨ (p4 ∧ p7)) ∧ ((p4 → False) → (p0 ∨ p4)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        have assump_26 : p3 := by
          exact assump_10
        let assump_18 := assump_6 assump_26
        apply False.elim assump_18
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p4 p0 p1 p2 : Prop)
theorem file7_34417 : (((((p2 ∧ True) ∧ (p0 ∧ p1)) → ((p4 → False) → (p4 → p1))) → False) → False) := by
  intro assump_10
  have assump_38 : (((p2 ∧ True) ∧ (p0 ∧ p1)) → ((p4 → False) → (p4 → p1))) := by
    intro assump_14
    intro assump_15
    intro assump_16
    cases assump_14
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        cases assump_22
        case intro assump_29 assump_30 =>
          exact assump_30
  let assump_13 := assump_10 assump_38
  apply False.elim assump_13


variable (p4 p3 p6 p7 p5 p2 p0 : Prop)
theorem file7_35003 : ((((((p3 → p7) ∨ (False ∨ p4)) → False) → (((p5 ∧ p0) ∧ (p7 ∨ p6)) → ((p7 → p0) ∨ (p2 → False)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p3 → p7) ∨ (False ∨ p4)) → False) → (((p5 ∧ p0) ∧ (p7 ∨ p6)) → ((p7 → p0) ∨ (p2 → False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_8
        case inl assump_15 =>
          apply Or.inl
          intro assump_21
          exact assump_10
        case inr assump_16 =>
          apply Or.inl
          intro assump_28
          exact assump_10
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p4 p2 p7 p5 p3 : Prop)
theorem file7_35771 : ((((((True ∧ True) ∨ (p2 ∨ p2)) ∧ ((True ∧ p4) → False)) ∧ (((p7 → p2) → (p4 ∨ False)) → False)) ∧ ((((True → p2) ∧ (p5 ∧ False)) → ((False ∨ p7) → False)) ∧ (((False → False) → False) ∧ ((p4 ∧ p3) ∧ (p5 → p7))))) → False) := by
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
          case intro assump_10 assump_11 =>
            cases assump_3
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    have assump_118 : (False → False) := by
                      intro assump_42
                      apply False.elim assump_42
                    let assump_41 := assump_24 assump_118
                    apply False.elim assump_41
        case inr assump_9 =>
          cases assump_9
          case inl assump_48 =>
            cases assump_3
            case intro assump_56 assump_57 =>
              cases assump_57
              case intro assump_60 assump_61 =>
                cases assump_61
                case intro assump_64 assump_65 =>
                  cases assump_64
                  case intro assump_66 assump_67 =>
                    have assump_119 : (False → False) := by
                      intro assump_78
                      apply False.elim assump_78
                    let assump_77 := assump_60 assump_119
                    apply False.elim assump_77
          case inr assump_49 =>
            cases assump_3
            case intro assump_90 assump_91 =>
              cases assump_91
              case intro assump_94 assump_95 =>
                cases assump_95
                case intro assump_98 assump_99 =>
                  cases assump_98
                  case intro assump_100 assump_101 =>
                    have assump_120 : (False → False) := by
                      intro assump_112
                      apply False.elim assump_112
                    let assump_111 := assump_94 assump_120
                    apply False.elim assump_111


variable (p3 p2 p7 p5 p0 p1 : Prop)
theorem file7_38200 : ((((((True → False) ∧ (p2 ∧ p3)) → ((p1 ∨ p1) → False)) → (((False → p7) → (p2 → False)) ∧ ((p2 → p2) → False))) ∧ ((((p1 → p5) ∨ (p7 ∨ p5)) → ((False → p0) ∨ (True → p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_32 : (((p1 → p5) ∨ (p7 ∨ p5)) → ((False → p0) ∨ (True → p0))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        apply Or.inl
        intro assump_14
        apply False.elim assump_14
      case inr assump_11 =>
        cases assump_11
        case inl assump_17 =>
          apply Or.inl
          intro assump_21
          apply False.elim assump_21
        case inr assump_18 =>
          apply Or.inl
          intro assump_26
          apply False.elim assump_26
    let assump_8 := assump_3 assump_32
    apply False.elim assump_8


variable (p7 p3 : Prop)
theorem file7_39101 : (((((True ∧ p3) ∧ (False ∧ p7)) → False) → False) → False) := by
  intro assump_9
  have assump_29 : (((True ∧ p3) ∧ (False ∧ p7)) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        cases assump_15
        case intro assump_22 assump_23 =>
          apply False.elim assump_22
  let assump_12 := assump_9 assump_29
  apply False.elim assump_12


variable (p2 p0 p6 p7 p5 p4 p3 : Prop)
theorem file7_39620 : ((((((True → p4) ∧ (p0 ∨ p5)) → ((p0 ∨ p7) → False)) → (((p7 → p6) → False) ∧ ((p2 ∧ True) ∨ (p6 → p3)))) ∧ ((((p5 → p4) ∧ (p3 → True)) ∧ ((p4 ∨ p7) ∧ (p6 → False))) ∧ (((False → p2) → False) ∧ ((False → False) → (p3 → p0))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_9
          case intro assump_16 assump_17 =>
            cases assump_16
            case inl assump_18 =>
              cases assump_7
              case intro assump_24 assump_25 =>
                have assump_64 : (False → p2) := by
                  intro assump_36
                  apply False.elim assump_36
                let assump_35 := assump_24 assump_64
                apply False.elim assump_35
            case inr assump_19 =>
              cases assump_7
              case intro assump_46 assump_47 =>
                have assump_65 : (False → p2) := by
                  intro assump_58
                  apply False.elim assump_58
                let assump_57 := assump_46 assump_65
                apply False.elim assump_57


variable (p0 p6 p4 p3 p7 p5 : Prop)
theorem file7_40942 : ((((((p7 ∨ True) → (False ∨ p4)) ∨ ((p0 → p3) → False)) ∧ (((False ∨ p7) → False) ∧ ((p5 ∧ p4) ∧ (p6 ∧ False)))) ∧ ((((False ∧ p7) ∨ (p7 → p4)) → False) → (((p0 ∧ p3) → False) ∨ ((p7 → False) → False)))) → False) := by
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
            cases assump_14
            case intro assump_16 assump_17 =>
              cases assump_15
              case intro assump_22 assump_23 =>
                apply False.elim assump_23
      case inr assump_7 =>
        cases assump_5
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              cases assump_35
              case intro assump_42 assump_43 =>
                apply False.elim assump_43


variable (p3 p5 p1 p4 p0 p2 : Prop)
theorem file7_42079 : (((((True → False) ∧ (True ∨ False)) ∧ ((p3 ∧ True) ∨ (p1 → False))) ∧ (((p4 ∧ p2) ∧ (False → True)) → False)) → ((((False ∧ p1) ∧ (True → False)) → ((True → p4) ∨ (p3 → p0))) ∧ (((p1 → False) ∨ (p5 → False)) → ((p5 → p2) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      apply False.elim assump_5
  intro assump_9
  intro assump_10
  cases assump_9
  case inl assump_13 =>
    cases assump_1
    case intro assump_17 assump_18 =>
      cases assump_17
      case intro assump_19 assump_20 =>
        cases assump_19
        case intro assump_21 assump_22 =>
          cases assump_22
          case inl assump_25 =>
            cases assump_20
            case inl assump_29 =>
              cases assump_29
              case intro assump_31 assump_32 =>
                have assump_99 : True := by
                  apply True.intro
                let assump_41 := assump_21 assump_99
                apply False.elim assump_41
            case inr assump_30 =>
              have assump_100 : True := by
                apply True.intro
              let assump_51 := assump_21 assump_100
              apply False.elim assump_51
          case inr assump_26 =>
            apply False.elim assump_26
  case inr assump_14 =>
    cases assump_1
    case intro assump_59 assump_60 =>
      cases assump_59
      case intro assump_61 assump_62 =>
        cases assump_61
        case intro assump_63 assump_64 =>
          cases assump_64
          case inl assump_67 =>
            cases assump_62
            case inl assump_71 =>
              cases assump_71
              case intro assump_73 assump_74 =>
                have assump_101 : True := by
                  apply True.intro
                let assump_83 := assump_63 assump_101
                apply False.elim assump_83
            case inr assump_72 =>
              have assump_102 : True := by
                apply True.intro
              let assump_93 := assump_63 assump_102
              apply False.elim assump_93
          case inr assump_68 =>
            apply False.elim assump_68


variable (p4 p2 p6 p5 : Prop)
theorem file7_44329 : (((((p4 ∨ p6) ∨ (p6 ∧ p5)) → False) ∧ (((p2 → False) → (False → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_16 : ((p2 → False) → (False → False)) := by
      intro assump_9
      intro assump_10
      apply False.elim assump_10
    let assump_8 := assump_3 assump_16
    apply False.elim assump_8


variable (p5 p2 p1 p7 p0 p3 : Prop)
theorem file7_44759 : ((((((p3 ∨ p0) ∨ (p0 → False)) → False) → (((p7 ∨ p2) ∧ (p5 → False)) → ((False → False) ∨ (p1 ∨ False)))) → False) → False) := by
  intro assump_1
  have assump_32 : ((((p3 ∨ p0) ∨ (p0 → False)) → False) → (((p7 ∨ p2) ∧ (p5 → False)) → ((False → False) ∨ (p1 ∨ False)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      cases assump_7
      case inl assump_9 =>
        apply Or.inl
        intro assump_17
        apply False.elim assump_17
      case inr assump_10 =>
        apply Or.inl
        intro assump_26
        apply False.elim assump_26
  let assump_4 := assump_1 assump_32
  apply False.elim assump_4


variable (p7 p5 p4 p2 p1 : Prop)
theorem file7_45488 : (((((False → False) → False) → False) ∨ (((False ∨ p1) → False) → False)) ∧ ((((p7 ∧ p5) → False) ∧ ((True ∧ p7) ∧ (p7 → True))) → (((False ∧ p4) → (p4 ∨ p4)) ∨ ((p4 ∧ False) → (p2 ∨ p5))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  have assump_31 : (False → False) := by
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_31
  apply False.elim assump_4
  intro assump_11
  cases assump_11
  case intro assump_12 assump_13 =>
    cases assump_13
    case intro assump_16 assump_17 =>
      cases assump_16
      case intro assump_18 assump_19 =>
        apply Or.inl
        intro assump_26
        cases assump_26
        case intro assump_27 assump_28 =>
          apply False.elim assump_27


variable (p7 p1 p5 p6 p2 p0 : Prop)
theorem file7_46290 : ((((((p7 → False) → False) → ((p0 ∧ p7) → (p2 → p5))) → (((False ∧ p1) ∨ (False ∧ True)) → ((p2 → False) → (p6 → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p7 → False) → False) → ((p0 ∧ p7) → (p2 → p5))) → (((False ∧ p1) ∨ (False ∧ True)) → ((p2 → False) → (p6 → False)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_6
    case inl assump_13 =>
      cases assump_13
      case intro assump_15 assump_16 =>
        apply False.elim assump_15
    case inr assump_14 =>
      cases assump_14
      case intro assump_19 assump_20 =>
        apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p2 p6 p0 : Prop)
theorem file7_47057 : (((((p0 ∧ p2) ∧ (False ∧ p6)) → False) → False) → False) := by
  intro assump_1
  have assump_21 : (((p0 ∧ p2) ∧ (False ∧ p6)) → False) := by
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


variable (p6 p4 p1 p0 p7 p3 p5 : Prop)
theorem file7_47562 : (((((p3 → p5) → False) ∧ ((p6 ∧ p6) ∧ (p3 → p5))) → (((True → p4) → False) ∨ ((p0 → p5) ∧ (False → p5)))) ∨ ((((p3 → False) → False) → False) → (((p1 ∨ p7) ∨ (p5 → False)) → ((p5 → p3) ∨ (p4 ∧ p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply Or.inl
        intro assump_16
        have assump_36 : (p3 → p5) := by
          intro assump_25
          have assump_37 : p3 := by
            exact assump_25
          let assump_31 := assump_7 assump_37
          exact assump_31
        let assump_24 := assump_2 assump_36
        apply False.elim assump_24


variable (p3 p2 p0 p5 p6 : Prop)
theorem file7_48350 : ((((((p5 → False) → (True ∨ p6)) ∧ ((p6 ∨ False) ∨ (False → False))) ∨ (((False ∨ p0) ∧ (p3 ∨ p0)) ∨ ((False → p2) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p5 → False) → (True ∨ p6)) ∧ ((p6 ∨ False) ∨ (False → False))) ∨ (((False ∨ p0) ∧ (p3 ∨ p0)) ∨ ((False → p2) → (p5 → False)))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    apply Or.inl
    apply True.intro
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p1 p7 p6 p5 p4 p0 : Prop)
theorem file7_48965 : (((((p1 → p6) → False) ∧ ((p6 ∨ p0) ∧ (False → False))) → (((True ∨ p1) ∧ (p6 ∨ p5)) ∨ ((p7 ∨ p5) → False))) → ((((False → p4) → (False ∧ p7)) → False) ∨ (((p7 ∧ p1) → False) ∧ ((True ∨ p1) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  have assump_15 : (False → p4) := by
    intro assump_8
    apply False.elim assump_8
  let assump_7 := assump_4 assump_15
  let assump_11 := And.left assump_7
  apply False.elim assump_11


variable (p2 p4 p7 p3 p1 p5 : Prop)
theorem file7_49472 : (((((p7 ∨ p5) ∧ (False ∧ p1)) → False) ∨ (((False → True) → False) → ((p2 ∧ p2) → False))) ∨ ((((p4 → p1) ∧ (False → False)) → ((p1 → False) ∧ (p5 ∨ False))) ∨ (((p3 → p7) ∨ (p1 ∧ p2)) → ((True → False) ∨ (p5 → False))))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
    case inr assump_5 =>
      cases assump_3
      case intro assump_14 assump_15 =>
        apply False.elim assump_14


variable (p2 p0 p1 p3 p6 p5 p4 : Prop)
theorem file7_50119 : ((((((p6 → True) ∧ (p1 ∧ p2)) → False) ∧ (((False ∧ p4) ∧ (False ∨ p3)) ∧ ((p1 → False) ∨ (True ∨ p0)))) ∨ ((((True ∨ p6) ∨ (p1 → False)) ∨ ((p5 ∧ p2) → (p3 ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            apply False.elim assump_12
  case inr assump_3 =>
    have assump_22 : (((True ∨ p6) ∨ (p1 → False)) ∨ ((p5 ∧ p2) → (p3 ∧ p6))) := by
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_18 := assump_3 assump_22
    apply False.elim assump_18


variable (p5 p2 p6 p7 : Prop)
theorem file7_50966 : ((((((p7 ∧ False) → (p2 → False)) ∨ ((p5 ∧ p2) ∧ (p7 → False))) → False) ∨ ((((True ∧ p6) → False) → ((p6 ∧ p7) → (p6 → False))) → (((p7 → False) → (p5 ∨ True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_47 : (((p7 ∧ False) → (p2 → False)) ∨ ((p5 ∧ p2) ∧ (p7 → False))) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      cases assump_7
      case intro assump_11 assump_12 =>
        apply False.elim assump_12
    let assump_6 := assump_2 assump_47
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_48 : (((True ∧ p6) → False) → ((p6 ∧ p7) → (p6 → False))) := by
      intro assump_23
      intro assump_24
      intro assump_25
      cases assump_24
      case intro assump_28 assump_29 =>
        have assump_49 : (True ∧ p6) := by
          apply And.intro
          apply True.intro
          exact assump_28
        let assump_36 := assump_23 assump_49
        apply False.elim assump_36
    let assump_22 := assump_3 assump_48
    have assump_50 : ((p7 → False) → (p5 ∨ True)) := by
      intro assump_41
      apply Or.inr
      apply True.intro
    let assump_40 := assump_22 assump_50
    apply False.elim assump_40


variable (p2 p3 p5 p6 p0 p7 : Prop)
theorem file7_52249 : ((((((p0 ∧ p3) ∨ (False → True)) ∧ ((p5 → p5) → (False ∧ p0))) ∧ (((p0 ∨ p5) → (p6 → False)) ∨ ((p5 ∨ p6) ∧ (False ∨ True)))) ∧ ((((p7 ∨ False) → (p0 → p2)) → ((p0 ∧ p0) ∨ (p3 → p5))) ∧ (((True ∨ p3) → False) ∧ ((False → True) ∧ (p7 → False))))) → False) := by
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
          case intro assump_10 assump_11 =>
            cases assump_5
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_23
                case intro assump_26 assump_27 =>
                  cases assump_27
                  case intro assump_30 assump_31 =>
                    have assump_190 : (True ∨ p3) := by
                      apply Or.inl
                      apply True.intro
                    let assump_38 := assump_26 assump_190
                    apply False.elim assump_38
            case inr assump_19 =>
              cases assump_19
              case intro assump_42 assump_43 =>
                cases assump_42
                case inl assump_44 =>
                  cases assump_43
                  case inl assump_48 =>
                    apply False.elim assump_48
                  case inr assump_49 =>
                    cases assump_3
                    case intro assump_54 assump_55 =>
                      cases assump_55
                      case intro assump_58 assump_59 =>
                        cases assump_59
                        case intro assump_62 assump_63 =>
                          have assump_191 : (True ∨ p3) := by
                            apply Or.inl
                            apply True.intro
                          let assump_70 := assump_58 assump_191
                          apply False.elim assump_70
                case inr assump_45 =>
                  cases assump_43
                  case inl assump_76 =>
                    apply False.elim assump_76
                  case inr assump_77 =>
                    cases assump_3
                    case intro assump_82 assump_83 =>
                      cases assump_83
                      case intro assump_86 assump_87 =>
                        cases assump_87
                        case intro assump_90 assump_91 =>
                          have assump_192 : (True ∨ p3) := by
                            apply Or.inl
                            apply True.intro
                          let assump_98 := assump_86 assump_192
                          apply False.elim assump_98
        case inr assump_9 =>
          cases assump_5
          case inl assump_106 =>
            cases assump_3
            case intro assump_110 assump_111 =>
              cases assump_111
              case intro assump_114 assump_115 =>
                cases assump_115
                case intro assump_118 assump_119 =>
                  have assump_193 : (True ∨ p3) := by
                    apply Or.inl
                    apply True.intro
                  let assump_126 := assump_114 assump_193
                  apply False.elim assump_126
          case inr assump_107 =>
            cases assump_107
            case intro assump_130 assump_131 =>
              cases assump_130
              case inl assump_132 =>
                cases assump_131
                case inl assump_136 =>
                  apply False.elim assump_136
                case inr assump_137 =>
                  cases assump_3
                  case intro assump_142 assump_143 =>
                    cases assump_143
                    case intro assump_146 assump_147 =>
                      cases assump_147
                      case intro assump_150 assump_151 =>
                        have assump_194 : (True ∨ p3) := by
                          apply Or.inl
                          apply True.intro
                        let assump_158 := assump_146 assump_194
                        apply False.elim assump_158
              case inr assump_133 =>
                cases assump_131
                case inl assump_164 =>
                  apply False.elim assump_164
                case inr assump_165 =>
                  cases assump_3
                  case intro assump_170 assump_171 =>
                    cases assump_171
                    case intro assump_174 assump_175 =>
                      cases assump_175
                      case intro assump_178 assump_179 =>
                        have assump_195 : (True ∨ p3) := by
                          apply Or.inl
                          apply True.intro
                        let assump_186 := assump_174 assump_195
                        apply False.elim assump_186


variable (p1 p4 p5 p2 p0 p7 p6 : Prop)
theorem file7_57206 : (((((p6 ∧ p7) ∧ (p7 → True)) ∨ ((True ∨ p0) ∨ (p2 → p5))) ∧ (((p1 → False) → (p7 → False)) ∧ ((False → p4) → False))) → ((((True ∧ p6) → False) ∨ ((p4 ∨ False) ∨ (p0 ∧ p4))) ∧ (((p2 → p6) → False) → ((p0 → p5) ∨ (p4 → False))))) := by
  intro assump_1
  apply And.intro
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_6
        case intro assump_8 assump_9 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            apply Or.inl
            intro assump_22
            cases assump_22
            case intro assump_23 assump_24 =>
              have assump_205 : (False → p4) := by
                intro assump_31
                apply False.elim assump_31
              let assump_30 := assump_17 assump_205
              apply False.elim assump_30
    case inr assump_5 =>
      cases assump_5
      case inl assump_37 =>
        cases assump_37
        case inl assump_39 =>
          cases assump_3
          case intro assump_43 assump_44 =>
            apply Or.inl
            intro assump_49
            cases assump_49
            case intro assump_50 assump_51 =>
              have assump_206 : (False → p4) := by
                intro assump_58
                apply False.elim assump_58
              let assump_57 := assump_44 assump_206
              apply False.elim assump_57
        case inr assump_40 =>
          cases assump_3
          case intro assump_66 assump_67 =>
            apply Or.inl
            intro assump_72
            cases assump_72
            case intro assump_73 assump_74 =>
              have assump_207 : (False → p4) := by
                intro assump_81
                apply False.elim assump_81
              let assump_80 := assump_67 assump_207
              apply False.elim assump_80
      case inr assump_38 =>
        cases assump_3
        case intro assump_89 assump_90 =>
          apply Or.inl
          intro assump_95
          cases assump_95
          case intro assump_96 assump_97 =>
            have assump_208 : (False → p4) := by
              intro assump_104
              apply False.elim assump_104
            let assump_103 := assump_90 assump_208
            apply False.elim assump_103
  intro assump_110
  cases assump_1
  case intro assump_113 assump_114 =>
    cases assump_113
    case inl assump_115 =>
      cases assump_115
      case intro assump_117 assump_118 =>
        cases assump_117
        case intro assump_119 assump_120 =>
          cases assump_114
          case intro assump_127 assump_128 =>
            apply Or.inl
            intro assump_133
            have assump_209 : (False → p4) := by
              intro assump_138
              apply False.elim assump_138
            let assump_137 := assump_128 assump_209
            apply False.elim assump_137
    case inr assump_116 =>
      cases assump_116
      case inl assump_144 =>
        cases assump_144
        case inl assump_146 =>
          cases assump_114
          case intro assump_150 assump_151 =>
            apply Or.inl
            intro assump_156
            have assump_210 : (False → p4) := by
              intro assump_161
              apply False.elim assump_161
            let assump_160 := assump_151 assump_210
            apply False.elim assump_160
        case inr assump_147 =>
          cases assump_114
          case intro assump_169 assump_170 =>
            apply Or.inl
            intro assump_175
            have assump_211 : (False → p4) := by
              intro assump_180
              apply False.elim assump_180
            let assump_179 := assump_170 assump_211
            apply False.elim assump_179
      case inr assump_145 =>
        cases assump_114
        case intro assump_188 assump_189 =>
          apply Or.inl
          intro assump_194
          have assump_212 : (False → p4) := by
            intro assump_199
            apply False.elim assump_199
          let assump_198 := assump_189 assump_212
          apply False.elim assump_198


variable (p2 p5 p4 p3 p7 p6 : Prop)
theorem file7_61378 : ((((((False ∧ p7) → (True ∨ p2)) → False) → (((p3 ∨ p4) → (p6 → p5)) → ((p3 ∧ True) → False))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((False ∧ p7) → (True ∨ p2)) → False) → (((p3 ∨ p4) → (p6 → p5)) → ((p3 ∧ True) → False))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    cases assump_7
    case intro assump_8 assump_9 =>
      have assump_31 : ((False ∧ p7) → (True ∨ p2)) := by
        intro assump_19
        cases assump_19
        case intro assump_20 assump_21 =>
          apply False.elim assump_20
      let assump_18 := assump_5 assump_31
      apply False.elim assump_18
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p5 p0 p7 p4 p3 p1 p2 p6 : Prop)
theorem file7_62135 : (((((False → p4) → False) ∧ ((p3 → False) ∧ (p7 ∨ p5))) → False) ∨ ((((True → p0) → (p7 ∨ True)) ∧ ((p7 ∨ p0) ∨ (True ∨ p6))) ∧ (((p3 → False) ∧ (p2 ∧ p6)) ∨ ((p1 ∧ p1) ∧ (p3 → False))))) := by
  apply Or.inl
  intro assump_22
  cases assump_22
  case intro assump_23 assump_24 =>
    cases assump_24
    case intro assump_27 assump_28 =>
      cases assump_28
      case inl assump_31 =>
        have assump_55 : (False → p4) := by
          intro assump_38
          apply False.elim assump_38
        let assump_37 := assump_23 assump_55
        apply False.elim assump_37
      case inr assump_32 =>
        have assump_56 : (False → p4) := by
          intro assump_49
          apply False.elim assump_49
        let assump_48 := assump_23 assump_56
        apply False.elim assump_48


variable (p7 p1 p2 p5 p3 p0 p4 p6 : Prop)
theorem file7_62992 : (((((p4 ∨ p0) → (p6 → p3)) → False) → (((p5 → p4) → (p3 ∨ p4)) ∨ ((False → p7) → False))) → ((((False ∧ p4) ∨ (p3 → p6)) → False) → (((p2 → False) → (p2 ∨ True)) ∨ ((False ∨ p1) → False)))) := by
  intro assump_1
  intro assump_2
  apply Or.inl
  intro assump_7
  apply Or.inr
  apply True.intro


variable (p0 p6 p2 p7 p5 p1 : Prop)
theorem file7_63348 : ((((((False ∧ True) ∧ (p6 → p0)) → False) ∨ (((p5 ∨ p2) ∨ (p2 ∧ p1)) ∨ ((True ∧ p7) ∨ (p0 ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_15 : ((((False ∧ True) ∧ (p6 → p0)) → False) ∨ (((p5 ∨ p2) ∨ (p2 ∧ p1)) ∨ ((True ∧ p7) ∨ (p0 ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_8
  let assump_4 := assump_1 assump_15
  apply False.elim assump_4


variable (p0 p1 p2 : Prop)
theorem file7_63910 : (((((p0 ∨ p2) → (True ∨ p1)) → False) → False) ∧ ((((True → False) → False) → False) → False)) := by
  apply And.intro
  intro assump_1
  have assump_29 : ((p0 ∨ p2) → (True ∨ p1)) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply True.intro
  let assump_4 := assump_1 assump_29
  apply False.elim assump_4
  intro assump_15
  have assump_30 : ((True → False) → False) := by
    intro assump_19
    have assump_31 : True := by
      apply True.intro
    let assump_22 := assump_19 assump_31
    apply False.elim assump_22
  let assump_18 := assump_15 assump_30
  apply False.elim assump_18


variable (p7 p1 p0 p6 p4 p3 p5 : Prop)
theorem file7_64680 : ((((((False → p6) → (p3 ∧ p4)) ∧ ((False → False) ∧ (p0 → False))) ∨ (((p5 → p4) → False) ∨ ((p4 → False) ∨ (p3 ∧ p5)))) ∧ ((((True ∨ p0) ∨ (p4 → False)) → False) ∧ (((p3 → False) ∧ (p3 ∨ p1)) ∨ ((p7 → p1) ∧ (p7 ∨ p1))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case intro assump_10 assump_11 =>
          cases assump_3
          case intro assump_16 assump_17 =>
            cases assump_17
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_23
                case inl assump_26 =>
                  have assump_229 : p3 := by
                    exact assump_26
                  let assump_31 := assump_22 assump_229
                  apply False.elim assump_31
                case inr assump_27 =>
                  have assump_230 : ((True ∨ p0) ∨ (p4 → False)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_39 := assump_16 assump_230
                  apply False.elim assump_39
            case inr assump_21 =>
              cases assump_21
              case intro assump_43 assump_44 =>
                cases assump_44
                case inl assump_47 =>
                  have assump_231 : ((True ∨ p0) ∨ (p4 → False)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_54 := assump_16 assump_231
                  apply False.elim assump_54
                case inr assump_48 =>
                  have assump_232 : ((True ∨ p0) ∨ (p4 → False)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_62 := assump_16 assump_232
                  apply False.elim assump_62
    case inr assump_5 =>
      cases assump_5
      case inl assump_66 =>
        cases assump_3
        case intro assump_70 assump_71 =>
          cases assump_71
          case inl assump_74 =>
            cases assump_74
            case intro assump_76 assump_77 =>
              cases assump_77
              case inl assump_80 =>
                have assump_233 : p3 := by
                  exact assump_80
                let assump_85 := assump_76 assump_233
                apply False.elim assump_85
              case inr assump_81 =>
                have assump_234 : ((True ∨ p0) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_93 := assump_70 assump_234
                apply False.elim assump_93
          case inr assump_75 =>
            cases assump_75
            case intro assump_97 assump_98 =>
              cases assump_98
              case inl assump_101 =>
                have assump_235 : ((True ∨ p0) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_108 := assump_70 assump_235
                apply False.elim assump_108
              case inr assump_102 =>
                have assump_236 : ((True ∨ p0) ∨ (p4 → False)) := by
                  apply Or.inl
                  apply Or.inl
                  apply True.intro
                let assump_116 := assump_70 assump_236
                apply False.elim assump_116
      case inr assump_67 =>
        cases assump_67
        case inl assump_120 =>
          cases assump_3
          case intro assump_124 assump_125 =>
            cases assump_125
            case inl assump_128 =>
              cases assump_128
              case intro assump_130 assump_131 =>
                cases assump_131
                case inl assump_134 =>
                  have assump_237 : p3 := by
                    exact assump_134
                  let assump_139 := assump_130 assump_237
                  apply False.elim assump_139
                case inr assump_135 =>
                  have assump_238 : ((True ∨ p0) ∨ (p4 → False)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_147 := assump_124 assump_238
                  apply False.elim assump_147
            case inr assump_129 =>
              cases assump_129
              case intro assump_151 assump_152 =>
                cases assump_152
                case inl assump_155 =>
                  have assump_239 : ((True ∨ p0) ∨ (p4 → False)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_162 := assump_124 assump_239
                  apply False.elim assump_162
                case inr assump_156 =>
                  have assump_240 : ((True ∨ p0) ∨ (p4 → False)) := by
                    apply Or.inl
                    apply Or.inl
                    apply True.intro
                  let assump_170 := assump_124 assump_240
                  apply False.elim assump_170
        case inr assump_121 =>
          cases assump_121
          case intro assump_174 assump_175 =>
            cases assump_3
            case intro assump_180 assump_181 =>
              cases assump_181
              case inl assump_184 =>
                cases assump_184
                case intro assump_186 assump_187 =>
                  cases assump_187
                  case inl assump_190 =>
                    have assump_241 : p3 := by
                      exact assump_190
                    let assump_195 := assump_186 assump_241
                    apply False.elim assump_195
                  case inr assump_191 =>
                    have assump_242 : p3 := by
                      exact assump_174
                    let assump_202 := assump_186 assump_242
                    apply False.elim assump_202
              case inr assump_185 =>
                cases assump_185
                case intro assump_206 assump_207 =>
                  cases assump_207
                  case inl assump_210 =>
                    have assump_243 : ((True ∨ p0) ∨ (p4 → False)) := by
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    let assump_217 := assump_180 assump_243
                    apply False.elim assump_217
                  case inr assump_211 =>
                    have assump_244 : ((True ∨ p0) ∨ (p4 → False)) := by
                      apply Or.inl
                      apply Or.inl
                      apply True.intro
                    let assump_225 := assump_180 assump_244
                    apply False.elim assump_225


variable (p3 p2 p7 p0 p1 p6 p5 : Prop)
theorem file7_71623 : (((((p3 → True) ∨ (p5 → False)) ∧ ((p5 → False) ∧ (p0 → p7))) ∧ (((p3 ∨ p3) ∧ (p1 → p3)) → False)) → ((((True → False) ∧ (p6 → False)) → False) ∨ (((p6 ∧ p7) → (p1 ∧ p6)) → ((p2 → False) → (p1 ∨ p7))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_5
        case intro assump_10 assump_11 =>
          apply Or.inl
          intro assump_18
          cases assump_18
          case intro assump_19 assump_20 =>
            have assump_52 : True := by
              apply True.intro
            let assump_26 := assump_19 assump_52
            apply False.elim assump_26
      case inr assump_7 =>
        cases assump_5
        case intro assump_32 assump_33 =>
          apply Or.inl
          intro assump_40
          cases assump_40
          case intro assump_41 assump_42 =>
            have assump_53 : True := by
              apply True.intro
            let assump_48 := assump_41 assump_53
            apply False.elim assump_48


variable (p5 p0 p3 p2 : Prop)
theorem file7_72770 : ((((((True ∨ p2) ∨ (p5 ∨ False)) ∨ ((False → False) ∨ (p0 → False))) ∨ (((p5 → False) → False) → ((p3 ∧ p3) → (p5 → False)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p2) ∨ (p5 ∨ False)) ∨ ((False → False) ∨ (p0 → False))) ∨ (((p5 → False) → False) → ((p3 ∧ p3) → (p5 → False)))) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 p2 p0 p3 p6 p1 p7 : Prop)
theorem file7_73301 : (((((p7 → p4) ∨ (p0 → p1)) → ((p0 → p7) ∧ (p3 ∧ True))) ∧ (((True → p3) ∨ (p2 → False)) ∧ ((p6 → False) → (p3 ∧ p0)))) → ((((p7 ∨ p2) ∨ (p6 ∧ p7)) ∨ ((True ∧ p6) ∧ (p3 ∨ p6))) → (((p1 ∧ p6) → (p0 ∧ True)) → ((p7 → True) ∨ (p3 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case inl assump_6 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_8
      case inl assump_10 =>
        cases assump_1
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              apply Or.inl
              intro assump_26
              apply True.intro
            case inr assump_21 =>
              apply Or.inl
              intro assump_31
              apply True.intro
      case inr assump_11 =>
        cases assump_1
        case intro assump_34 assump_35 =>
          cases assump_35
          case intro assump_38 assump_39 =>
            cases assump_38
            case inl assump_40 =>
              apply Or.inl
              intro assump_46
              apply True.intro
            case inr assump_41 =>
              apply Or.inl
              intro assump_51
              apply True.intro
    case inr assump_9 =>
      cases assump_9
      case intro assump_52 assump_53 =>
        cases assump_1
        case intro assump_58 assump_59 =>
          cases assump_59
          case intro assump_62 assump_63 =>
            cases assump_62
            case inl assump_64 =>
              apply Or.inl
              intro assump_70
              apply True.intro
            case inr assump_65 =>
              apply Or.inl
              intro assump_75
              apply True.intro
  case inr assump_7 =>
    cases assump_7
    case intro assump_76 assump_77 =>
      cases assump_76
      case intro assump_78 assump_79 =>
        cases assump_77
        case inl assump_84 =>
          cases assump_1
          case intro assump_88 assump_89 =>
            cases assump_89
            case intro assump_92 assump_93 =>
              cases assump_92
              case inl assump_94 =>
                apply Or.inl
                intro assump_100
                apply True.intro
              case inr assump_95 =>
                apply Or.inl
                intro assump_105
                apply True.intro
        case inr assump_85 =>
          cases assump_1
          case intro assump_108 assump_109 =>
            cases assump_109
            case intro assump_112 assump_113 =>
              cases assump_112
              case inl assump_114 =>
                apply Or.inl
                intro assump_120
                apply True.intro
              case inr assump_115 =>
                apply Or.inl
                intro assump_125
                apply True.intro


variable (p4 p1 p5 p2 p3 p0 p6 : Prop)
theorem file7_76232 : (((((p4 → False) → (False → p6)) → False) ∧ (((False ∧ p0) ∨ (False → False)) ∧ ((False → p3) ∨ (p4 → False)))) → ((((False ∧ p1) ∨ (p4 ∧ p0)) → ((p5 ∧ p2) ∨ (p1 → p3))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case intro assump_9 assump_10 =>
      cases assump_9
      case inl assump_11 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          apply False.elim assump_13
      case inr assump_12 =>
        cases assump_10
        case inl assump_19 =>
          have assump_45 : ((p4 → False) → (False → p6)) := by
            intro assump_26
            intro assump_27
            apply False.elim assump_27
          let assump_25 := assump_5 assump_45
          apply False.elim assump_25
        case inr assump_20 =>
          have assump_46 : ((p4 → False) → (False → p6)) := by
            intro assump_38
            intro assump_39
            apply False.elim assump_39
          let assump_37 := assump_5 assump_46
          apply False.elim assump_37


variable (p5 p0 p1 p6 : Prop)
theorem file7_77359 : (((((True → p0) ∨ (p0 → p5)) ∧ ((p0 → False) ∧ (False ∧ p1))) ∧ (((p1 → p6) → (p6 → False)) → False)) → False) := by
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
            apply False.elim assump_14
      case inr assump_7 =>
        cases assump_5
        case intro assump_20 assump_21 =>
          cases assump_21
          case intro assump_24 assump_25 =>
            apply False.elim assump_24


variable (p5 p0 p3 p7 p4 p2 p1 : Prop)
theorem file7_78085 : (((((p4 ∨ p4) ∧ (p1 → False)) → ((p7 ∨ p2) → (p5 ∧ p4))) → (((True → False) ∧ (True → False)) → ((p7 → False) ∨ (p3 ∧ False)))) ∨ ((((p7 ∧ p5) → False) → ((p0 → p1) ∨ (True → p4))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    apply Or.inl
    intro assump_11
    have assump_20 : True := by
      apply True.intro
    let assump_16 := assump_4 assump_20
    apply False.elim assump_16


variable (p5 p7 p1 p2 p3 p4 p6 : Prop)
theorem file7_78608 : ((((((False → p1) ∨ (p5 ∨ p4)) → False) ∧ (((p7 → False) → (p2 → True)) ∨ ((p5 ∧ p1) ∨ (p7 → p6)))) ∧ ((((False ∧ p6) ∨ (True → False)) → ((p4 ∨ p3) → False)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case inl assump_8 =>
        have assump_136 : (((False ∧ p6) ∨ (True → False)) → ((p4 ∨ p3) → False)) := by
          intro assump_15
          intro assump_16
          cases assump_16
          case inl assump_17 =>
            cases assump_15
            case inl assump_21 =>
              cases assump_21
              case intro assump_23 assump_24 =>
                apply False.elim assump_23
            case inr assump_22 =>
              have assump_137 : True := by
                apply True.intro
              let assump_29 := assump_22 assump_137
              apply False.elim assump_29
          case inr assump_18 =>
            cases assump_15
            case inl assump_35 =>
              cases assump_35
              case intro assump_37 assump_38 =>
                apply False.elim assump_37
            case inr assump_36 =>
              have assump_138 : True := by
                apply True.intro
              let assump_43 := assump_36 assump_138
              apply False.elim assump_43
        let assump_14 := assump_3 assump_136
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case inl assump_50 =>
          cases assump_50
          case intro assump_52 assump_53 =>
            have assump_139 : (((False ∧ p6) ∨ (True → False)) → ((p4 ∨ p3) → False)) := by
              intro assump_61
              intro assump_62
              cases assump_62
              case inl assump_63 =>
                cases assump_61
                case inl assump_67 =>
                  cases assump_67
                  case intro assump_69 assump_70 =>
                    apply False.elim assump_69
                case inr assump_68 =>
                  have assump_140 : True := by
                    apply True.intro
                  let assump_75 := assump_68 assump_140
                  apply False.elim assump_75
              case inr assump_64 =>
                cases assump_61
                case inl assump_81 =>
                  cases assump_81
                  case intro assump_83 assump_84 =>
                    apply False.elim assump_83
                case inr assump_82 =>
                  have assump_141 : True := by
                    apply True.intro
                  let assump_89 := assump_82 assump_141
                  apply False.elim assump_89
            let assump_60 := assump_3 assump_139
            apply False.elim assump_60
        case inr assump_51 =>
          have assump_142 : (((False ∧ p6) ∨ (True → False)) → ((p4 ∨ p3) → False)) := by
            intro assump_101
            intro assump_102
            cases assump_102
            case inl assump_103 =>
              cases assump_101
              case inl assump_107 =>
                cases assump_107
                case intro assump_109 assump_110 =>
                  apply False.elim assump_109
              case inr assump_108 =>
                have assump_143 : True := by
                  apply True.intro
                let assump_115 := assump_108 assump_143
                apply False.elim assump_115
            case inr assump_104 =>
              cases assump_101
              case inl assump_121 =>
                cases assump_121
                case intro assump_123 assump_124 =>
                  apply False.elim assump_123
              case inr assump_122 =>
                have assump_144 : True := by
                  apply True.intro
                let assump_129 := assump_122 assump_144
                apply False.elim assump_129
          let assump_100 := assump_3 assump_142
          apply False.elim assump_100


variable (p5 p2 p1 p4 p6 p7 p3 : Prop)
theorem file7_82647 : (((((p4 → p5) → (p6 → p7)) ∧ ((p5 ∨ p2) → False)) ∧ (((p7 → p3) → False) ∧ ((p7 → False) ∧ (p1 → False)))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_3
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          have assump_35 : (p7 → p3) := by
            intro assump_23
            have assump_36 : p7 := by
              exact assump_23
            let assump_28 := assump_14 assump_36
            apply False.elim assump_28
          let assump_22 := assump_10 assump_35
          apply False.elim assump_22


variable (p0 p1 p5 p4 p6 p2 p7 p3 : Prop)
theorem file7_83396 : (((((p3 ∧ p2) → (p4 ∧ p5)) → False) ∧ (((False ∧ p1) ∧ (p2 ∨ True)) ∧ ((True ∧ p6) ∧ (p7 ∨ p0)))) → ((((p7 → p1) → False) → False) ∨ (((p5 → p5) → False) → ((p5 ∧ p5) ∧ (False ∨ p5))))) := by
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


variable (p3 p5 p1 p4 : Prop)
theorem file7_83926 : ((((((True ∨ p3) ∨ (p4 → True)) ∨ ((p4 → False) → False)) ∨ (((True → p5) → (p1 → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_8 : ((((True ∨ p3) ∨ (p4 → True)) ∨ ((p4 → False) → False)) ∨ (((True → p5) → (p1 → False)) → False)) := by
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


variable (p4 : Prop)
theorem file7_84387 : ((((((p4 → True) → False) → False) ∧ (((p4 ∧ False) ∧ (True → False)) → False)) → False) → False) := by
  intro assump_1
  have assump_25 : ((((p4 → True) → False) → False) ∧ (((p4 ∧ False) ∧ (True → False)) → False)) := by
    apply And.intro
    intro assump_5
    have assump_26 : (p4 → True) := by
      intro assump_9
      apply True.intro
    let assump_8 := assump_5 assump_26
    apply False.elim assump_8
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
  let assump_4 := assump_1 assump_25
  apply False.elim assump_4


variable (p0 p2 p5 p3 p4 p6 p1 p7 : Prop)
theorem file7_85108 : ((((((p1 → False) ∧ (p0 → False)) → ((p6 ∧ p0) ∨ (p3 ∧ True))) ∨ (((p4 ∨ False) → False) → ((p2 → False) → False))) ∧ ((((p6 ∨ True) ∨ (p2 → False)) → False) ∧ (((p7 ∨ False) ∧ (p2 ∧ p5)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        have assump_32 : ((p6 ∨ True) ∨ (p2 → False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_15 := assump_8 assump_32
        apply False.elim assump_15
    case inr assump_5 =>
      cases assump_3
      case intro assump_21 assump_22 =>
        have assump_33 : ((p6 ∨ True) ∨ (p2 → False)) := by
          apply Or.inl
          apply Or.inr
          apply True.intro
        let assump_28 := assump_21 assump_33
        apply False.elim assump_28


variable (p5 p6 p7 p4 p0 p2 : Prop)
theorem file7_86064 : (((((p0 → p6) ∨ (p2 ∨ p7)) → False) → False) → ((((p7 ∨ False) ∨ (False → False)) ∨ ((p7 → True) ∧ (p4 ∧ p6))) ∨ (((p4 → False) ∨ (True ∨ p5)) → ((p0 ∧ p6) → False)))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_4
  apply False.elim assump_4


variable (p5 p3 p6 p2 p0 p4 : Prop)
theorem file7_86405 : ((((((p4 ∧ p0) → False) ∧ ((False ∧ p5) ∧ (p4 → p6))) → (((p3 ∧ p2) ∨ (False → False)) → ((True → p0) → (p6 ∨ p0)))) → False) → False) := by
  intro assump_13
  have assump_55 : ((((p4 ∧ p0) → False) ∧ ((False ∧ p5) ∧ (p4 → p6))) → (((p3 ∧ p2) ∨ (False → False)) → ((True → p0) → (p6 ∨ p0)))) := by
    intro assump_17
    intro assump_18
    intro assump_19
    cases assump_18
    case inl assump_22 =>
      cases assump_22
      case intro assump_24 assump_25 =>
        cases assump_17
        case intro assump_30 assump_31 =>
          cases assump_31
          case intro assump_34 assump_35 =>
            cases assump_34
            case intro assump_36 assump_37 =>
              apply False.elim assump_36
    case inr assump_23 =>
      cases assump_17
      case intro assump_42 assump_43 =>
        cases assump_43
        case intro assump_46 assump_47 =>
          cases assump_46
          case intro assump_48 assump_49 =>
            apply False.elim assump_48
  let assump_16 := assump_13 assump_55
  apply False.elim assump_16


variable (p0 p5 p3 p1 p4 p2 p7 : Prop)
theorem file7_87517 : ((((((p5 ∨ p0) → (p4 → p3)) ∨ ((p4 ∨ p2) ∨ (p4 ∨ True))) ∨ (((p5 → p7) ∧ (p1 ∨ p4)) → False)) ∧ ((((p1 ∧ p0) → (p3 → True)) ∧ ((p3 → False) ∧ (False ∨ True))) ∧ (((p1 ∧ p0) → (p2 → p1)) → False))) → False) := by
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
              case inl assump_20 =>
                apply False.elim assump_20
              case inr assump_21 =>
                have assump_218 : ((p1 ∧ p0) → (p2 → p1)) := by
                  intro assump_29
                  intro assump_30
                  cases assump_29
                  case intro assump_33 assump_34 =>
                    exact assump_33
                let assump_28 := assump_11 assump_218
                apply False.elim assump_28
      case inr assump_7 =>
        cases assump_7
        case inl assump_42 =>
          cases assump_42
          case inl assump_44 =>
            cases assump_3
            case intro assump_48 assump_49 =>
              cases assump_48
              case intro assump_50 assump_51 =>
                cases assump_51
                case intro assump_54 assump_55 =>
                  cases assump_55
                  case inl assump_58 =>
                    apply False.elim assump_58
                  case inr assump_59 =>
                    have assump_219 : ((p1 ∧ p0) → (p2 → p1)) := by
                      intro assump_67
                      intro assump_68
                      cases assump_67
                      case intro assump_71 assump_72 =>
                        exact assump_71
                    let assump_66 := assump_49 assump_219
                    apply False.elim assump_66
          case inr assump_45 =>
            cases assump_3
            case intro assump_82 assump_83 =>
              cases assump_82
              case intro assump_84 assump_85 =>
                cases assump_85
                case intro assump_88 assump_89 =>
                  cases assump_89
                  case inl assump_92 =>
                    apply False.elim assump_92
                  case inr assump_93 =>
                    have assump_220 : ((p1 ∧ p0) → (p2 → p1)) := by
                      intro assump_101
                      intro assump_102
                      cases assump_101
                      case intro assump_105 assump_106 =>
                        exact assump_105
                    let assump_100 := assump_83 assump_220
                    apply False.elim assump_100
        case inr assump_43 =>
          cases assump_43
          case inl assump_114 =>
            cases assump_3
            case intro assump_118 assump_119 =>
              cases assump_118
              case intro assump_120 assump_121 =>
                cases assump_121
                case intro assump_124 assump_125 =>
                  cases assump_125
                  case inl assump_128 =>
                    apply False.elim assump_128
                  case inr assump_129 =>
                    have assump_221 : ((p1 ∧ p0) → (p2 → p1)) := by
                      intro assump_137
                      intro assump_138
                      cases assump_137
                      case intro assump_141 assump_142 =>
                        exact assump_141
                    let assump_136 := assump_119 assump_221
                    apply False.elim assump_136
          case inr assump_115 =>
            cases assump_3
            case intro assump_152 assump_153 =>
              cases assump_152
              case intro assump_154 assump_155 =>
                cases assump_155
                case intro assump_158 assump_159 =>
                  cases assump_159
                  case inl assump_162 =>
                    apply False.elim assump_162
                  case inr assump_163 =>
                    have assump_222 : ((p1 ∧ p0) → (p2 → p1)) := by
                      intro assump_171
                      intro assump_172
                      cases assump_171
                      case intro assump_175 assump_176 =>
                        exact assump_175
                    let assump_170 := assump_153 assump_222
                    apply False.elim assump_170
    case inr assump_5 =>
      cases assump_3
      case intro assump_186 assump_187 =>
        cases assump_186
        case intro assump_188 assump_189 =>
          cases assump_189
          case intro assump_192 assump_193 =>
            cases assump_193
            case inl assump_196 =>
              apply False.elim assump_196
            case inr assump_197 =>
              have assump_223 : ((p1 ∧ p0) → (p2 → p1)) := by
                intro assump_205
                intro assump_206
                cases assump_205
                case intro assump_209 assump_210 =>
                  exact assump_209
              let assump_204 := assump_187 assump_223
              apply False.elim assump_204


variable (p5 p3 p7 p6 p0 p4 p2 p1 : Prop)
theorem file7_92825 : (((((p7 → p5) → (p0 ∧ p7)) → ((False → False) ∨ (p6 ∧ p2))) → False) → ((((p4 ∧ False) → (p3 ∧ p6)) → ((p5 → p1) → (p5 → False))) ∧ (((True ∧ p5) → (False → False)) ∨ ((p4 → p1) → False)))) := by
  intro assump_1
  apply And.intro
  intro assump_2
  intro assump_3
  intro assump_4
  have assump_29 : (((p7 → p5) → (p0 ∧ p7)) → ((False → False) ∨ (p6 ∧ p2))) := by
    intro assump_14
    apply Or.inl
    intro assump_17
    apply False.elim assump_17
  let assump_13 := assump_1 assump_29
  apply False.elim assump_13
  apply Or.inl
  intro assump_25
  intro assump_26
  apply False.elim assump_26


variable (p2 p1 p5 p7 p6 p0 : Prop)
theorem file7_93485 : ((((((p6 ∧ p1) → False) ∧ ((False → False) → False)) → (((p0 ∧ p0) ∧ (p5 ∨ p2)) ∨ ((True ∧ p7) ∨ (p0 → False)))) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p6 ∧ p1) → False) ∧ ((False → False) → False)) → (((p0 ∧ p0) ∧ (p5 ∨ p2)) ∨ ((True ∧ p7) ∨ (p0 → False)))) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply Or.inr
      apply Or.inr
      intro assump_12
      have assump_27 : (False → False) := by
        intro assump_17
        apply False.elim assump_17
      let assump_16 := assump_7 assump_27
      apply False.elim assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p1 p2 p7 p0 : Prop)
theorem file7_94207 : ((((((p0 → p7) ∧ (False ∧ p1)) ∧ ((True → False) → False)) → (((False ∧ p7) → (p2 ∨ p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_22 : ((((p0 → p7) ∧ (False ∧ p1)) ∧ ((True → False) → False)) → (((False ∧ p7) → (p2 ∨ p0)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_12
        case intro assump_15 assump_16 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p4 p2 p6 p7 p3 p5 : Prop)
theorem file7_94852 : (((((p6 → False) → False) → False) → (((p7 ∧ p5) → (p6 → False)) ∨ ((True → False) → False))) → ((((p2 → p6) → (p5 ∨ True)) ∨ ((False → False) → (True ∨ p5))) ∨ (((p7 ∨ p5) ∧ (p3 ∨ p3)) ∧ ((p4 → False) ∨ (p4 ∨ False))))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  apply Or.inr
  apply True.intro


variable (p5 p6 p3 p0 p2 : Prop)
theorem file7_95234 : ((((((p0 ∨ True) ∨ (True ∧ p2)) → False) → (((p0 → p0) ∨ (p3 → p5)) ∨ ((p6 → True) → False))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p0 ∨ True) ∨ (True ∧ p2)) → False) → (((p0 → p0) ∨ (p3 → p5)) ∨ ((p6 → True) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p7 p0 p6 p2 p4 p1 p3 : Prop)
theorem file7_95705 : (((((p1 → True) → False) → ((p3 ∧ False) ∧ (p6 → False))) → (((p6 ∧ p6) ∨ (p2 ∨ p7)) ∨ ((True ∨ p0) ∨ (p4 ∧ False)))) ∨ ((((p2 ∧ p7) ∨ (p1 ∨ p0)) → ((True → p6) ∨ (p1 → False))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inr
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p7 p4 p1 p5 p3 p0 : Prop)
theorem file7_96055 : ((((((p4 → False) → (p7 → p0)) ∨ ((p3 → False) ∨ (p5 ∧ p4))) ∨ (((p3 ∧ p0) → False) → False)) ∧ ((((p1 → False) → (p7 ∧ p3)) → ((False → False) ∨ (p1 ∧ p7))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        have assump_70 : (((p1 → False) → (p7 ∧ p3)) → ((False → False) ∨ (p1 ∧ p7))) := by
          intro assump_13
          apply Or.inl
          intro assump_16
          apply False.elim assump_16
        let assump_12 := assump_3 assump_70
        apply False.elim assump_12
      case inr assump_7 =>
        cases assump_7
        case inl assump_22 =>
          have assump_71 : (((p1 → False) → (p7 ∧ p3)) → ((False → False) ∨ (p1 ∧ p7))) := by
            intro assump_29
            apply Or.inl
            intro assump_32
            apply False.elim assump_32
          let assump_28 := assump_3 assump_71
          apply False.elim assump_28
        case inr assump_23 =>
          cases assump_23
          case intro assump_38 assump_39 =>
            have assump_72 : (((p1 → False) → (p7 ∧ p3)) → ((False → False) ∨ (p1 ∧ p7))) := by
              intro assump_47
              apply Or.inl
              intro assump_50
              apply False.elim assump_50
            let assump_46 := assump_3 assump_72
            apply False.elim assump_46
    case inr assump_5 =>
      have assump_73 : (((p1 → False) → (p7 ∧ p3)) → ((False → False) ∨ (p1 ∧ p7))) := by
        intro assump_61
        apply Or.inl
        intro assump_64
        apply False.elim assump_64
      let assump_60 := assump_3 assump_73
      apply False.elim assump_60


variable (p0 p6 p4 p7 p3 p5 : Prop)
theorem file7_97823 : (((((True ∧ p0) ∧ (p4 → p3)) ∨ ((p7 → p6) → (True ∨ p5))) → False) → ((((p4 → False) → False) ∧ ((p3 ∨ False) → False)) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    have assump_18 : (((True ∧ p0) ∧ (p4 → p3)) ∨ ((p7 → p6) → (True ∨ p5))) := by
      apply Or.inr
      intro assump_12
      apply Or.inl
      apply True.intro
    let assump_11 := assump_1 assump_18
    apply False.elim assump_11


variable (p4 p5 p7 p0 p3 p6 : Prop)
theorem file7_98341 : (((((False → False) ∨ (p3 → p5)) ∧ ((True ∨ p5) ∨ (p4 ∨ p3))) ∨ (((p7 → False) ∨ (p5 ∨ p0)) → False)) ∨ ((((p4 → False) → False) ∧ ((p6 → p7) ∨ (True ∧ p0))) ∨ (((p4 → False) ∨ (False ∧ p0)) ∧ ((p7 ∨ False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  apply Or.inl
  intro assump_1
  apply False.elim assump_1
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p0 p3 p6 p1 p7 p2 p4 : Prop)
theorem file7_98786 : ((((((p3 → True) → (p3 ∨ p4)) ∧ ((p0 → True) → (p6 ∧ p6))) ∧ (((p1 ∨ p3) → False) ∧ ((p1 → False) ∨ (p1 → False)))) ∧ ((((False ∧ p7) → False) ∨ ((p2 ∧ p1) → (p6 → False))) → False)) → False) := by
  intro assump_23
  cases assump_23
  case intro assump_24 assump_25 =>
    cases assump_24
    case intro assump_26 assump_27 =>
      cases assump_26
      case intro assump_28 assump_29 =>
        cases assump_27
        case intro assump_34 assump_35 =>
          cases assump_35
          case inl assump_38 =>
            have assump_66 : (((False ∧ p7) → False) ∨ ((p2 ∧ p1) → (p6 → False))) := by
              apply Or.inl
              intro assump_45
              cases assump_45
              case intro assump_46 assump_47 =>
                apply False.elim assump_46
            let assump_44 := assump_25 assump_66
            apply False.elim assump_44
          case inr assump_39 =>
            have assump_67 : (((False ∧ p7) → False) ∨ ((p2 ∧ p1) → (p6 → False))) := by
              apply Or.inl
              intro assump_58
              cases assump_58
              case intro assump_59 assump_60 =>
                apply False.elim assump_59
            let assump_57 := assump_25 assump_67
            apply False.elim assump_57


variable (p2 p3 : Prop)
theorem file7_100090 : (((((False → False) → (p2 → False)) → ((p3 ∨ p2) ∨ (False → p2))) → False) → False) := by
  intro assump_1
  have assump_14 : (((False → False) → (p2 → False)) → ((p3 ∨ p2) ∨ (False → p2))) := by
    intro assump_5
    apply Or.inr
    intro assump_8
    apply False.elim assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p5 p0 p3 p4 p1 p7 p2 : Prop)
theorem file7_100499 : ((((((True → False) ∧ (p0 ∧ True)) ∧ ((p4 → p1) ∨ (p1 ∧ p3))) → (((p1 ∨ p2) ∧ (p2 ∨ False)) ∧ ((p5 ∨ p7) → False))) → False) → False) := by
  intro assump_13
  have assump_161 : ((((True → False) ∧ (p0 ∧ True)) ∧ ((p4 → p1) ∨ (p1 ∧ p3))) → (((p1 ∨ p2) ∧ (p2 ∨ False)) ∧ ((p5 ∨ p7) → False))) := by
    intro assump_17
    apply And.intro
    apply And.intro
    cases assump_17
    case intro assump_18 assump_19 =>
      cases assump_18
      case intro assump_20 assump_21 =>
        cases assump_21
        case intro assump_24 assump_25 =>
          cases assump_19
          case inl assump_30 =>
            have assump_162 : True := by
              apply True.intro
            let assump_36 := assump_20 assump_162
            apply False.elim assump_36
          case inr assump_31 =>
            cases assump_31
            case intro assump_40 assump_41 =>
              apply Or.inl
              exact assump_40
    cases assump_17
    case intro assump_46 assump_47 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        cases assump_49
        case intro assump_52 assump_53 =>
          cases assump_47
          case inl assump_58 =>
            have assump_163 : True := by
              apply True.intro
            let assump_64 := assump_48 assump_163
            apply False.elim assump_64
          case inr assump_59 =>
            cases assump_59
            case intro assump_68 assump_69 =>
              have assump_164 : True := by
                apply True.intro
              let assump_77 := assump_48 assump_164
              apply False.elim assump_77
    intro assump_81
    cases assump_81
    case inl assump_82 =>
      cases assump_17
      case intro assump_86 assump_87 =>
        cases assump_86
        case intro assump_88 assump_89 =>
          cases assump_89
          case intro assump_92 assump_93 =>
            cases assump_87
            case inl assump_98 =>
              have assump_165 : True := by
                apply True.intro
              let assump_104 := assump_88 assump_165
              apply False.elim assump_104
            case inr assump_99 =>
              cases assump_99
              case intro assump_108 assump_109 =>
                have assump_166 : True := by
                  apply True.intro
                let assump_117 := assump_88 assump_166
                apply False.elim assump_117
    case inr assump_83 =>
      cases assump_17
      case intro assump_123 assump_124 =>
        cases assump_123
        case intro assump_125 assump_126 =>
          cases assump_126
          case intro assump_129 assump_130 =>
            cases assump_124
            case inl assump_135 =>
              have assump_167 : True := by
                apply True.intro
              let assump_141 := assump_125 assump_167
              apply False.elim assump_141
            case inr assump_136 =>
              cases assump_136
              case intro assump_145 assump_146 =>
                have assump_168 : True := by
                  apply True.intro
                let assump_154 := assump_125 assump_168
                apply False.elim assump_154
  let assump_16 := assump_13 assump_161
  apply False.elim assump_16


variable (p6 p3 p2 p1 p4 p7 p0 : Prop)
theorem file7_103791 : (((((p7 ∧ p0) ∧ (p1 ∧ p2)) → ((p7 ∧ True) → (p4 → False))) → (((p3 ∧ p6) → (False ∨ False)) → ((p4 → p1) → (False → False)))) ∨ ((((p0 ∧ p7) → (p6 → p7)) → ((False ∧ p2) ∨ (p2 ∧ p4))) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  apply False.elim assump_4


variable (p5 p4 p0 p1 p2 p6 : Prop)
theorem file7_104162 : (((((p0 ∨ p4) → False) → ((p4 ∧ False) → (p6 → p4))) → False) → ((((p2 ∨ p6) → False) ∨ ((p5 ∧ p6) ∨ (p1 ∨ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    have assump_72 : (((p0 ∨ p4) → False) → ((p4 ∧ False) → (p6 → p4))) := by
      intro assump_10
      intro assump_11
      intro assump_12
      cases assump_11
      case intro assump_15 assump_16 =>
        apply False.elim assump_16
    let assump_9 := assump_1 assump_72
    apply False.elim assump_9
  case inr assump_4 =>
    cases assump_4
    case inl assump_24 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        have assump_73 : (((p0 ∨ p4) → False) → ((p4 ∧ False) → (p6 → p4))) := by
          intro assump_35
          intro assump_36
          intro assump_37
          cases assump_36
          case intro assump_40 assump_41 =>
            apply False.elim assump_41
        let assump_34 := assump_1 assump_73
        apply False.elim assump_34
    case inr assump_25 =>
      cases assump_25
      case inl assump_49 =>
        have assump_74 : (((p0 ∨ p4) → False) → ((p4 ∧ False) → (p6 → p4))) := by
          intro assump_56
          intro assump_57
          intro assump_58
          cases assump_57
          case intro assump_61 assump_62 =>
            apply False.elim assump_62
        let assump_55 := assump_1 assump_74
        apply False.elim assump_55
      case inr assump_50 =>
        apply False.elim assump_50


variable (p6 p0 p2 p5 p3 p7 : Prop)
theorem file7_105703 : (((((p5 → False) → (p0 → False)) → ((p2 → p6) ∧ (p7 ∧ p0))) ∧ (((p3 ∧ False) ∨ (p3 → p3)) → False)) → False) := by
  intro assump_25
  cases assump_25
  case intro assump_26 assump_27 =>
    have assump_39 : ((p3 ∧ False) ∨ (p3 → p3)) := by
      apply Or.inr
      intro assump_33
      exact assump_33
    let assump_32 := assump_27 assump_39
    apply False.elim assump_32


variable (p0 p2 p4 p1 p7 : Prop)
theorem file7_106136 : ((((((True ∧ False) → False) ∧ ((True ∧ p2) → (p2 ∨ p0))) ∨ (((False → False) ∧ (p7 ∨ p4)) → ((p1 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True ∧ False) → False) ∧ ((True ∧ p2) → (p2 ∨ p0))) ∨ (((False → False) ∧ (p7 ∨ p4)) → ((p1 → False) → False))) := by
    apply Or.inl
    apply And.intro
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      apply False.elim assump_7
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      apply Or.inl
      exact assump_14
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p6 p2 p1 p5 p7 p0 p3 p4 : Prop)
theorem file7_106829 : (((((p0 ∨ p3) ∨ (p3 ∨ False)) ∧ ((p4 ∨ p2) → (p4 → p1))) → (((p1 → p6) ∧ (p2 ∨ p2)) → ((False → False) ∨ (p1 ∧ p0)))) ∧ ((((True → True) ∧ (p7 ∨ p2)) → False) → (((p6 ∧ p7) ∧ (True ∧ p7)) → ((p6 ∧ p5) ∨ (p6 → False))))) := by
  apply And.intro
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case inl assump_7 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_13
          case inl assump_15 =>
            apply Or.inl
            intro assump_21
            apply False.elim assump_21
          case inr assump_16 =>
            apply Or.inl
            intro assump_28
            apply False.elim assump_28
        case inr assump_14 =>
          cases assump_14
          case inl assump_31 =>
            apply Or.inl
            intro assump_37
            apply False.elim assump_37
          case inr assump_32 =>
            apply False.elim assump_32
    case inr assump_8 =>
      cases assump_1
      case intro assump_44 assump_45 =>
        cases assump_44
        case inl assump_46 =>
          cases assump_46
          case inl assump_48 =>
            apply Or.inl
            intro assump_54
            apply False.elim assump_54
          case inr assump_49 =>
            apply Or.inl
            intro assump_61
            apply False.elim assump_61
        case inr assump_47 =>
          cases assump_47
          case inl assump_64 =>
            apply Or.inl
            intro assump_70
            apply False.elim assump_70
          case inr assump_65 =>
            apply False.elim assump_65
  intro assump_75
  intro assump_76
  cases assump_76
  case intro assump_77 assump_78 =>
    cases assump_77
    case intro assump_79 assump_80 =>
      cases assump_78
      case intro assump_85 assump_86 =>
        apply Or.inr
        intro assump_93
        have assump_102 : ((True → True) ∧ (p7 ∨ p2)) := by
          apply And.intro
          intro assump_98
          apply True.intro
          apply Or.inl
          exact assump_86
        let assump_97 := assump_75 assump_102
        apply False.elim assump_97


variable (p0 p7 p2 p1 p5 : Prop)
theorem file7_109088 : ((((((p1 ∧ p2) → False) → False) ∧ (((p7 → False) ∨ (p2 ∨ p5)) → False)) ∧ ((((p2 → False) ∧ (p0 ∧ False)) → False) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      have assump_27 : (((p2 → False) ∧ (p0 ∧ False)) → False) := by
        intro assump_13
        cases assump_13
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply False.elim assump_19
      let assump_12 := assump_3 assump_27
      apply False.elim assump_12


variable (p7 p1 p5 p2 p3 p0 p6 : Prop)
theorem file7_109758 : (((((False → False) ∧ (p1 → False)) → False) ∨ (((p7 ∧ p5) → (p3 → False)) ∨ ((p2 → True) → False))) → ((((True → False) → False) ∨ ((True → p5) ∧ (p2 ∧ p2))) ∨ (((p6 ∨ p0) → (p0 ∨ p2)) → False))) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    apply Or.inl
    apply Or.inl
    intro assump_6
    have assump_33 : True := by
      apply True.intro
    let assump_9 := assump_6 assump_33
    apply False.elim assump_9
  case inr assump_3 =>
    cases assump_3
    case inl assump_13 =>
      apply Or.inl
      apply Or.inl
      intro assump_17
      have assump_34 : True := by
        apply True.intro
      let assump_20 := assump_17 assump_34
      apply False.elim assump_20
    case inr assump_14 =>
      apply Or.inl
      apply Or.inl
      intro assump_26
      have assump_35 : True := by
        apply True.intro
      let assump_29 := assump_26 assump_35
      apply False.elim assump_29


variable (p5 p0 p2 p1 p6 p7 p3 p4 : Prop)
theorem file7_110745 : (((((p2 → False) ∧ (p1 → False)) ∨ ((True → False) ∧ (p4 → p5))) ∧ (((p3 → False) ∧ (p1 ∧ p3)) ∧ ((p5 ∧ p2) → False))) → ((((p3 → False) ∨ (False ∨ p5)) ∨ ((p5 ∧ False) → False)) → (((p7 ∧ p6) ∨ (p0 ∨ p2)) → ((p6 → False) ∨ (p2 → False))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_2
      case inl assump_12 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_1
          case intro assump_18 assump_19 =>
            cases assump_18
            case inl assump_20 =>
              cases assump_20
              case intro assump_22 assump_23 =>
                cases assump_19
                case intro assump_28 assump_29 =>
                  cases assump_28
                  case intro assump_30 assump_31 =>
                    cases assump_31
                    case intro assump_34 assump_35 =>
                      apply Or.inl
                      intro assump_42
                      have assump_648 : p3 := by
                        exact assump_35
                      let assump_49 := assump_30 assump_648
                      apply False.elim assump_49
            case inr assump_21 =>
              cases assump_21
              case intro assump_53 assump_54 =>
                cases assump_19
                case intro assump_59 assump_60 =>
                  cases assump_59
                  case intro assump_61 assump_62 =>
                    cases assump_62
                    case intro assump_65 assump_66 =>
                      apply Or.inl
                      intro assump_73
                      have assump_649 : p3 := by
                        exact assump_66
                      let assump_80 := assump_61 assump_649
                      apply False.elim assump_80
        case inr assump_15 =>
          cases assump_15
          case inl assump_84 =>
            apply False.elim assump_84
          case inr assump_85 =>
            cases assump_1
            case intro assump_90 assump_91 =>
              cases assump_90
              case inl assump_92 =>
                cases assump_92
                case intro assump_94 assump_95 =>
                  cases assump_91
                  case intro assump_100 assump_101 =>
                    cases assump_100
                    case intro assump_102 assump_103 =>
                      cases assump_103
                      case intro assump_106 assump_107 =>
                        apply Or.inl
                        intro assump_114
                        have assump_650 : p3 := by
                          exact assump_107
                        let assump_121 := assump_102 assump_650
                        apply False.elim assump_121
              case inr assump_93 =>
                cases assump_93
                case intro assump_125 assump_126 =>
                  cases assump_91
                  case intro assump_131 assump_132 =>
                    cases assump_131
                    case intro assump_133 assump_134 =>
                      cases assump_134
                      case intro assump_137 assump_138 =>
                        apply Or.inl
                        intro assump_145
                        have assump_651 : p3 := by
                          exact assump_138
                        let assump_152 := assump_133 assump_651
                        apply False.elim assump_152
      case inr assump_13 =>
        cases assump_1
        case intro assump_158 assump_159 =>
          cases assump_158
          case inl assump_160 =>
            cases assump_160
            case intro assump_162 assump_163 =>
              cases assump_159
              case intro assump_168 assump_169 =>
                cases assump_168
                case intro assump_170 assump_171 =>
                  cases assump_171
                  case intro assump_174 assump_175 =>
                    apply Or.inl
                    intro assump_182
                    have assump_652 : p3 := by
                      exact assump_175
                    let assump_189 := assump_170 assump_652
                    apply False.elim assump_189
          case inr assump_161 =>
            cases assump_161
            case intro assump_193 assump_194 =>
              cases assump_159
              case intro assump_199 assump_200 =>
                cases assump_199
                case intro assump_201 assump_202 =>
                  cases assump_202
                  case intro assump_205 assump_206 =>
                    apply Or.inl
                    intro assump_213
                    have assump_653 : p3 := by
                      exact assump_206
                    let assump_220 := assump_201 assump_653
                    apply False.elim assump_220
  case inr assump_5 =>
    cases assump_5
    case inl assump_224 =>
      cases assump_2
      case inl assump_228 =>
        cases assump_228
        case inl assump_230 =>
          cases assump_1
          case intro assump_234 assump_235 =>
            cases assump_234
            case inl assump_236 =>
              cases assump_236
              case intro assump_238 assump_239 =>
                cases assump_235
                case intro assump_244 assump_245 =>
                  cases assump_244
                  case intro assump_246 assump_247 =>
                    cases assump_247
                    case intro assump_250 assump_251 =>
                      apply Or.inl
                      intro assump_258
                      have assump_654 : p3 := by
                        exact assump_251
                      let assump_265 := assump_246 assump_654
                      apply False.elim assump_265
            case inr assump_237 =>
              cases assump_237
              case intro assump_269 assump_270 =>
                cases assump_235
                case intro assump_275 assump_276 =>
                  cases assump_275
                  case intro assump_277 assump_278 =>
                    cases assump_278
                    case intro assump_281 assump_282 =>
                      apply Or.inl
                      intro assump_289
                      have assump_655 : p3 := by
                        exact assump_282
                      let assump_296 := assump_277 assump_655
                      apply False.elim assump_296
        case inr assump_231 =>
          cases assump_231
          case inl assump_300 =>
            apply False.elim assump_300
          case inr assump_301 =>
            cases assump_1
            case intro assump_306 assump_307 =>
              cases assump_306
              case inl assump_308 =>
                cases assump_308
                case intro assump_310 assump_311 =>
                  cases assump_307
                  case intro assump_316 assump_317 =>
                    cases assump_316
                    case intro assump_318 assump_319 =>
                      cases assump_319
                      case intro assump_322 assump_323 =>
                        apply Or.inl
                        intro assump_330
                        have assump_656 : p3 := by
                          exact assump_323
                        let assump_337 := assump_318 assump_656
                        apply False.elim assump_337
              case inr assump_309 =>
                cases assump_309
                case intro assump_341 assump_342 =>
                  cases assump_307
                  case intro assump_347 assump_348 =>
                    cases assump_347
                    case intro assump_349 assump_350 =>
                      cases assump_350
                      case intro assump_353 assump_354 =>
                        apply Or.inl
                        intro assump_361
                        have assump_657 : p3 := by
                          exact assump_354
                        let assump_368 := assump_349 assump_657
                        apply False.elim assump_368
      case inr assump_229 =>
        cases assump_1
        case intro assump_374 assump_375 =>
          cases assump_374
          case inl assump_376 =>
            cases assump_376
            case intro assump_378 assump_379 =>
              cases assump_375
              case intro assump_384 assump_385 =>
                cases assump_384
                case intro assump_386 assump_387 =>
                  cases assump_387
                  case intro assump_390 assump_391 =>
                    apply Or.inl
                    intro assump_398
                    have assump_658 : p3 := by
                      exact assump_391
                    let assump_405 := assump_386 assump_658
                    apply False.elim assump_405
          case inr assump_377 =>
            cases assump_377
            case intro assump_409 assump_410 =>
              cases assump_375
              case intro assump_415 assump_416 =>
                cases assump_415
                case intro assump_417 assump_418 =>
                  cases assump_418
                  case intro assump_421 assump_422 =>
                    apply Or.inl
                    intro assump_429
                    have assump_659 : p3 := by
                      exact assump_422
                    let assump_436 := assump_417 assump_659
                    apply False.elim assump_436
    case inr assump_225 =>
      cases assump_2
      case inl assump_442 =>
        cases assump_442
        case inl assump_444 =>
          cases assump_1
          case intro assump_448 assump_449 =>
            cases assump_448
            case inl assump_450 =>
              cases assump_450
              case intro assump_452 assump_453 =>
                cases assump_449
                case intro assump_458 assump_459 =>
                  cases assump_458
                  case intro assump_460 assump_461 =>
                    cases assump_461
                    case intro assump_464 assump_465 =>
                      apply Or.inl
                      intro assump_472
                      have assump_660 : p3 := by
                        exact assump_465
                      let assump_479 := assump_460 assump_660
                      apply False.elim assump_479
            case inr assump_451 =>
              cases assump_451
              case intro assump_483 assump_484 =>
                cases assump_449
                case intro assump_489 assump_490 =>
                  cases assump_489
                  case intro assump_491 assump_492 =>
                    cases assump_492
                    case intro assump_495 assump_496 =>
                      apply Or.inl
                      intro assump_503
                      have assump_661 : p3 := by
                        exact assump_496
                      let assump_510 := assump_491 assump_661
                      apply False.elim assump_510
        case inr assump_445 =>
          cases assump_445
          case inl assump_514 =>
            apply False.elim assump_514
          case inr assump_515 =>
            cases assump_1
            case intro assump_520 assump_521 =>
              cases assump_520
              case inl assump_522 =>
                cases assump_522
                case intro assump_524 assump_525 =>
                  cases assump_521
                  case intro assump_530 assump_531 =>
                    cases assump_530
                    case intro assump_532 assump_533 =>
                      cases assump_533
                      case intro assump_536 assump_537 =>
                        apply Or.inl
                        intro assump_544
                        have assump_662 : (p5 ∧ p2) := by
                          apply And.intro
                          exact assump_515
                          exact assump_225
                        let assump_548 := assump_531 assump_662
                        apply False.elim assump_548
              case inr assump_523 =>
                cases assump_523
                case intro assump_552 assump_553 =>
                  cases assump_521
                  case intro assump_558 assump_559 =>
                    cases assump_558
                    case intro assump_560 assump_561 =>
                      cases assump_561
                      case intro assump_564 assump_565 =>
                        apply Or.inl
                        intro assump_572
                        have assump_663 : (p5 ∧ p2) := by
                          apply And.intro
                          exact assump_515
                          exact assump_225
                        let assump_576 := assump_559 assump_663
                        apply False.elim assump_576
      case inr assump_443 =>
        cases assump_1
        case intro assump_582 assump_583 =>
          cases assump_582
          case inl assump_584 =>
            cases assump_584
            case intro assump_586 assump_587 =>
              cases assump_583
              case intro assump_592 assump_593 =>
                cases assump_592
                case intro assump_594 assump_595 =>
                  cases assump_595
                  case intro assump_598 assump_599 =>
                    apply Or.inl
                    intro assump_606
                    have assump_664 : p3 := by
                      exact assump_599
                    let assump_613 := assump_594 assump_664
                    apply False.elim assump_613
          case inr assump_585 =>
            cases assump_585
            case intro assump_617 assump_618 =>
              cases assump_583
              case intro assump_623 assump_624 =>
                cases assump_623
                case intro assump_625 assump_626 =>
                  cases assump_626
                  case intro assump_629 assump_630 =>
                    apply Or.inl
                    intro assump_637
                    have assump_665 : p3 := by
                      exact assump_630
                    let assump_644 := assump_625 assump_665
                    apply False.elim assump_644


variable (p1 p6 p2 p5 : Prop)
theorem file7_125072 : (((((p5 → True) → False) ∨ ((p2 ∨ True) → False)) ∧ (((p6 ∧ False) → False) ∧ ((p5 ∧ p1) → False))) → False) := by
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      cases assump_16
      case intro assump_21 assump_22 =>
        have assump_48 : (p5 → True) := by
          intro assump_30
          apply True.intro
        let assump_29 := assump_17 assump_48
        apply False.elim assump_29
    case inr assump_18 =>
      cases assump_16
      case intro assump_36 assump_37 =>
        have assump_49 : (p2 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_44 := assump_18 assump_49
        apply False.elim assump_44


variable (p7 p4 p0 p6 p3 : Prop)
theorem file7_125861 : ((((((p0 ∨ p4) ∨ (False ∧ p7)) ∨ ((p0 → p6) → (True → p0))) ∧ (((p0 ∨ p3) ∧ (True → False)) → ((p4 → False) ∧ (p6 → p3)))) ∧ ((((p4 → p0) ∨ (p6 → p4)) → ((p6 ∧ p6) → (p7 → True))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          cases assump_8
          case inl assump_10 =>
            have assump_55 : (((p4 → p0) ∨ (p6 → p4)) → ((p6 ∧ p6) → (p7 → True))) := by
              intro assump_19
              intro assump_20
              intro assump_21
              apply True.intro
            let assump_18 := assump_3 assump_55
            apply False.elim assump_18
          case inr assump_11 =>
            have assump_56 : (((p4 → p0) ∨ (p6 → p4)) → ((p6 ∧ p6) → (p7 → True))) := by
              intro assump_32
              intro assump_33
              intro assump_34
              apply True.intro
            let assump_31 := assump_3 assump_56
            apply False.elim assump_31
        case inr assump_9 =>
          cases assump_9
          case intro assump_38 assump_39 =>
            apply False.elim assump_38
      case inr assump_7 =>
        have assump_57 : (((p4 → p0) ∨ (p6 → p4)) → ((p6 ∧ p6) → (p7 → True))) := by
          intro assump_49
          intro assump_50
          intro assump_51
          apply True.intro
        let assump_48 := assump_3 assump_57
        apply False.elim assump_48


variable (p2 p6 p5 p4 p7 : Prop)
theorem file7_127462 : (((((False → False) → (True → False)) → False) → False) → ((((p2 → p4) → False) ∨ ((p5 → p5) ∧ (p7 ∧ p2))) → (((False ∨ True) → (p7 ∨ p5)) ∨ ((False → False) → (p6 → False))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    apply Or.inl
    intro assump_9
    cases assump_9
    case inl assump_10 =>
      apply False.elim assump_10
    case inr assump_11 =>
      have assump_50 : (((False → False) → (True → False)) → False) := by
        intro assump_17
        have assump_51 : (False → False) := by
          intro assump_21
          apply False.elim assump_21
        let assump_20 := assump_17 assump_51
        have assump_52 : True := by
          apply True.intro
        let assump_24 := assump_20 assump_52
        apply False.elim assump_24
      let assump_16 := assump_1 assump_50
      apply False.elim assump_16
  case inr assump_4 =>
    cases assump_4
    case intro assump_31 assump_32 =>
      cases assump_32
      case intro assump_35 assump_36 =>
        apply Or.inl
        intro assump_43
        cases assump_43
        case inl assump_44 =>
          apply False.elim assump_44
        case inr assump_45 =>
          apply Or.inl
          exact assump_35


variable (p7 p4 p5 p6 p2 p0 : Prop)
theorem file7_128747 : ((((((p7 ∨ p4) → (p6 → False)) ∧ ((True ∨ p2) ∨ (p0 ∧ False))) ∧ (((p2 ∨ p7) ∨ (p5 → False)) → ((p6 ∨ p2) → (p4 ∧ p6)))) ∧ ((((p0 ∧ p5) ∨ (p5 ∧ p2)) ∧ ((p0 ∧ p7) ∧ (p2 → False))) ∧ (((p0 → p0) ∨ (p0 → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_7
        case inl assump_10 =>
          cases assump_10
          case inl assump_12 =>
            cases assump_3
            case intro assump_18 assump_19 =>
              cases assump_18
              case intro assump_20 assump_21 =>
                cases assump_20
                case inl assump_22 =>
                  cases assump_22
                  case intro assump_24 assump_25 =>
                    cases assump_21
                    case intro assump_30 assump_31 =>
                      cases assump_30
                      case intro assump_32 assump_33 =>
                        have assump_140 : ((p0 → p0) ∨ (p0 → False)) := by
                          apply Or.inl
                          intro assump_43
                          exact assump_43
                        let assump_42 := assump_19 assump_140
                        apply False.elim assump_42
                case inr assump_23 =>
                  cases assump_23
                  case intro assump_49 assump_50 =>
                    cases assump_21
                    case intro assump_55 assump_56 =>
                      cases assump_55
                      case intro assump_57 assump_58 =>
                        have assump_141 : ((p0 → p0) ∨ (p0 → False)) := by
                          apply Or.inl
                          intro assump_68
                          exact assump_68
                        let assump_67 := assump_19 assump_141
                        apply False.elim assump_67
          case inr assump_13 =>
            cases assump_3
            case intro assump_78 assump_79 =>
              cases assump_78
              case intro assump_80 assump_81 =>
                cases assump_80
                case inl assump_82 =>
                  cases assump_82
                  case intro assump_84 assump_85 =>
                    cases assump_81
                    case intro assump_90 assump_91 =>
                      cases assump_90
                      case intro assump_92 assump_93 =>
                        have assump_142 : ((p0 → p0) ∨ (p0 → False)) := by
                          apply Or.inl
                          intro assump_103
                          exact assump_103
                        let assump_102 := assump_79 assump_142
                        apply False.elim assump_102
                case inr assump_83 =>
                  cases assump_83
                  case intro assump_109 assump_110 =>
                    cases assump_81
                    case intro assump_115 assump_116 =>
                      cases assump_115
                      case intro assump_117 assump_118 =>
                        have assump_143 : ((p0 → p0) ∨ (p0 → False)) := by
                          apply Or.inl
                          intro assump_128
                          exact assump_128
                        let assump_127 := assump_79 assump_143
                        apply False.elim assump_127
        case inr assump_11 =>
          cases assump_11
          case intro assump_134 assump_135 =>
            apply False.elim assump_135


variable (p7 p5 p4 : Prop)
theorem file7_132357 : ((((((False → False) ∧ (False ∧ True)) ∧ ((p5 ∨ p7) ∨ (p4 ∨ p5))) → False) → False) → False) := by
  intro assump_1
  have assump_19 : ((((False → False) ∧ (False ∧ True)) ∧ ((p5 ∨ p7) ∨ (p4 ∨ p5))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case intro assump_12 assump_13 =>
          apply False.elim assump_12
  let assump_4 := assump_1 assump_19
  apply False.elim assump_4


variable (p5 p3 p7 p1 p0 : Prop)
theorem file7_132928 : (((((p0 ∨ p5) ∧ (p5 → p7)) ∧ ((True ∧ p3) → False)) ∧ (((False ∨ p0) → False) ∧ ((p1 ∨ p5) → False))) → False) := by
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
            have assump_43 : (False ∨ p0) := by
              apply Or.inr
              exact assump_8
            let assump_23 := assump_16 assump_43
            apply False.elim assump_23
        case inr assump_9 =>
          cases assump_3
          case intro assump_33 assump_34 =>
            have assump_44 : (p1 ∨ p5) := by
              apply Or.inr
              exact assump_9
            let assump_39 := assump_34 assump_44
            apply False.elim assump_39


variable (p0 p2 p7 p1 p3 : Prop)
theorem file7_133884 : ((((((False ∧ p0) ∧ (p3 → False)) ∧ ((p2 ∨ False) ∧ (p7 ∧ True))) ∨ (((True ∨ True) ∨ (p7 → True)) ∨ ((p3 ∨ p2) ∨ (p3 ∧ p1)))) → False) → False) := by
  intro assump_1
  have assump_8 : ((((False ∧ p0) ∧ (p3 → False)) ∧ ((p2 ∨ False) ∧ (p7 ∧ True))) ∨ (((True ∨ True) ∨ (p7 → True)) ∨ ((p3 ∨ p2) ∨ (p3 ∧ p1)))) := by
    apply Or.inr
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_8
  apply False.elim assump_4


