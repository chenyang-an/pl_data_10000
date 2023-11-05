variable (p7 p1 p2 p5 p3 p4 p6 p0 : Prop)
theorem file75_50 : (((((p7 → p1) → (p6 → p0)) → ((p2 → False) → False)) ∧ (((p4 → False) ∧ (p1 ∨ p6)) ∨ ((p6 ∧ False) ∧ (p3 ∨ p3)))) → ((((p6 → p7) ∧ (p2 ∧ p0)) → ((False → p7) ∧ (False ∨ True))) ∨ (((True ∨ p6) ∨ (p5 → False)) ∨ ((True → False) → False)))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          apply And.intro
          intro assump_17
          apply False.elim assump_17
          cases assump_16
          case intro assump_20 assump_21 =>
            cases assump_21
            case intro assump_24 assump_25 =>
              apply Or.inr
              apply True.intro
        case inr assump_13 =>
          apply Or.inl
          intro assump_32
          apply And.intro
          intro assump_33
          apply False.elim assump_33
          cases assump_32
          case intro assump_36 assump_37 =>
            cases assump_37
            case intro assump_40 assump_41 =>
              apply Or.inr
              apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_46 assump_47 =>
        cases assump_46
        case intro assump_48 assump_49 =>
          apply False.elim assump_49


variable (p0 p6 p7 p5 p4 p1 p2 p3 : Prop)
theorem file75_1484 : (((((p7 → p6) ∧ (p5 ∧ p4)) → ((p1 → p5) ∨ (True ∧ p7))) ∨ (((p0 ∨ False) → False) → ((p0 ∨ p6) ∨ (p0 → p3)))) ∨ ((((p3 ∧ p2) → False) ∧ ((p0 ∨ False) → (p7 ∧ p4))) → False)) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      apply Or.inl
      intro assump_12
      exact assump_6


variable (p0 p7 p1 p2 p3 p4 p6 p5 : Prop)
theorem file75_1945 : (((((p2 → False) → False) ∨ ((p3 → p6) → False)) ∨ (((p0 → False) ∨ (False ∧ p3)) → ((False ∨ True) → (p7 → p6)))) → ((((True ∧ True) ∧ (p1 ∧ p0)) ∧ ((p1 → False) ∨ (p4 → p5))) → (((p5 ∨ p3) → False) → ((False ∧ p5) ∨ (p3 → p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case intro assump_8 assump_9 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        cases assump_9
        case intro assump_16 assump_17 =>
          cases assump_7
          case inl assump_22 =>
            cases assump_1
            case inl assump_26 =>
              cases assump_26
              case inl assump_28 =>
                apply Or.inr
                intro assump_32
                exact assump_16
              case inr assump_29 =>
                apply Or.inr
                intro assump_37
                exact assump_16
            case inr assump_27 =>
              apply Or.inr
              intro assump_42
              exact assump_16
          case inr assump_23 =>
            cases assump_1
            case inl assump_47 =>
              cases assump_47
              case inl assump_49 =>
                apply Or.inr
                intro assump_53
                exact assump_16
              case inr assump_50 =>
                apply Or.inr
                intro assump_58
                exact assump_16
            case inr assump_48 =>
              apply Or.inr
              intro assump_63
              exact assump_16


variable (p5 p3 p2 p4 p0 p7 p1 p6 : Prop)
theorem file75_3561 : (((((p4 ∧ p2) → False) → False) ∧ (((p1 → False) ∨ (p1 → False)) ∨ ((True → p4) ∧ (p6 → False)))) → ((((p3 → True) ∨ (p0 ∧ p4)) ∧ ((p2 ∨ p7) → (False → p1))) → (((p4 → False) → False) ∨ ((p5 → p2) → (p1 ∨ True))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case inl assump_5 =>
      cases assump_1
      case intro assump_11 assump_12 =>
        cases assump_12
        case inl assump_15 =>
          cases assump_15
          case inl assump_17 =>
            apply Or.inl
            intro assump_21
            have assump_144 : ((p4 ∧ p2) → False) := by
              intro assump_27
              cases assump_27
              case intro assump_28 assump_29 =>
                have assump_145 : p4 := by
                  exact assump_28
                let assump_36 := assump_21 assump_145
                apply False.elim assump_36
            let assump_26 := assump_11 assump_144
            apply False.elim assump_26
          case inr assump_18 =>
            apply Or.inl
            intro assump_45
            have assump_146 : ((p4 ∧ p2) → False) := by
              intro assump_51
              cases assump_51
              case intro assump_52 assump_53 =>
                have assump_147 : p4 := by
                  exact assump_52
                let assump_60 := assump_45 assump_147
                apply False.elim assump_60
            let assump_50 := assump_11 assump_146
            apply False.elim assump_50
        case inr assump_16 =>
          cases assump_16
          case intro assump_67 assump_68 =>
            apply Or.inl
            intro assump_73
            have assump_148 : ((p4 ∧ p2) → False) := by
              intro assump_81
              cases assump_81
              case intro assump_82 assump_83 =>
                have assump_149 : p4 := by
                  exact assump_82
                let assump_90 := assump_73 assump_149
                apply False.elim assump_90
            let assump_80 := assump_11 assump_148
            apply False.elim assump_80
    case inr assump_6 =>
      cases assump_6
      case intro assump_97 assump_98 =>
        cases assump_1
        case intro assump_105 assump_106 =>
          cases assump_106
          case inl assump_109 =>
            cases assump_109
            case inl assump_111 =>
              apply Or.inl
              intro assump_115
              have assump_150 : p4 := by
                exact assump_98
              let assump_118 := assump_115 assump_150
              apply False.elim assump_118
            case inr assump_112 =>
              apply Or.inl
              intro assump_124
              have assump_151 : p4 := by
                exact assump_98
              let assump_127 := assump_124 assump_151
              apply False.elim assump_127
          case inr assump_110 =>
            cases assump_110
            case intro assump_131 assump_132 =>
              apply Or.inl
              intro assump_137
              have assump_152 : p4 := by
                exact assump_98
              let assump_140 := assump_137 assump_152
              apply False.elim assump_140


variable (p4 p7 p5 p2 p0 p6 : Prop)
theorem file75_6819 : (((((p4 ∧ p2) → (p0 → True)) → False) → False) ∨ ((((p7 ∧ p2) ∨ (p6 ∨ p2)) → False) → (((p5 ∨ p2) ∨ (p7 → p0)) → False))) := by
  apply Or.inl
  intro assump_13
  have assump_22 : ((p4 ∧ p2) → (p0 → True)) := by
    intro assump_17
    intro assump_18
    apply True.intro
  let assump_16 := assump_13 assump_22
  apply False.elim assump_16


variable (p5 p6 p4 p2 : Prop)
theorem file75_7214 : (((((False → False) → False) → ((p4 ∨ True) → (p5 ∧ p5))) → (((p2 ∧ p2) ∧ (p2 → False)) ∧ ((p6 → True) ∧ (False ∨ p2)))) → False) := by
  intro assump_15
  have assump_145 : (((False → False) → False) → ((p4 ∨ True) → (p5 ∧ p5))) := by
    intro assump_19
    intro assump_20
    apply And.intro
    cases assump_20
    case inl assump_21 =>
      have assump_146 : (False → False) := by
        intro assump_28
        apply False.elim assump_28
      let assump_27 := assump_19 assump_146
      apply False.elim assump_27
    case inr assump_22 =>
      have assump_147 : (False → False) := by
        intro assump_39
        apply False.elim assump_39
      let assump_38 := assump_19 assump_147
      apply False.elim assump_38
    cases assump_20
    case inl assump_45 =>
      have assump_148 : (False → False) := by
        intro assump_52
        apply False.elim assump_52
      let assump_51 := assump_19 assump_148
      apply False.elim assump_51
    case inr assump_46 =>
      have assump_149 : (False → False) := by
        intro assump_63
        apply False.elim assump_63
      let assump_62 := assump_19 assump_149
      apply False.elim assump_62
  let assump_18 := assump_15 assump_145
  let assump_69 := And.right assump_18
  let assump_75 := And.right assump_69
  cases assump_75
  case inl assump_78 =>
    apply False.elim assump_78
  case inr assump_79 =>
    have assump_150 : (((False → False) → False) → ((p4 ∨ True) → (p5 ∧ p5))) := by
      intro assump_86
      intro assump_87
      apply And.intro
      cases assump_87
      case inl assump_88 =>
        have assump_151 : (False → False) := by
          intro assump_95
          apply False.elim assump_95
        let assump_94 := assump_86 assump_151
        apply False.elim assump_94
      case inr assump_89 =>
        have assump_152 : (False → False) := by
          intro assump_106
          apply False.elim assump_106
        let assump_105 := assump_86 assump_152
        apply False.elim assump_105
      cases assump_87
      case inl assump_112 =>
        have assump_153 : (False → False) := by
          intro assump_119
          apply False.elim assump_119
        let assump_118 := assump_86 assump_153
        apply False.elim assump_118
      case inr assump_113 =>
        have assump_154 : (False → False) := by
          intro assump_130
          apply False.elim assump_130
        let assump_129 := assump_86 assump_154
        apply False.elim assump_129
    let assump_85 := assump_15 assump_150
    let assump_136 := And.left assump_85
    let assump_137 := And.right assump_136
    have assump_155 : p2 := by
      exact assump_79
    let assump_141 := assump_137 assump_155
    apply False.elim assump_141


variable (p7 p1 p5 p6 p2 p0 p3 : Prop)
theorem file75_10003 : ((((((p3 ∨ p2) → False) → ((p5 ∧ p0) ∨ (p2 → p6))) → (((p5 ∨ p1) → False) ∧ ((p7 ∧ p7) → (p3 ∧ p3)))) ∧ ((((p7 → False) ∧ (p0 ∧ p0)) ∧ ((p0 → False) ∧ (True → False))) ∧ (((p1 ∨ p0) ∨ (p1 → p0)) → False))) → False) := by
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
            cases assump_9
            case intro assump_20 assump_21 =>
              have assump_32 : ((p1 ∨ p0) ∨ (p1 → p0)) := by
                apply Or.inl
                apply Or.inr
                exact assump_15
              let assump_28 := assump_7 assump_32
              apply False.elim assump_28


variable (p1 p4 p6 p5 p7 p2 p3 p0 : Prop)
theorem file75_10922 : (((((p5 ∧ p6) ∨ (p3 → True)) → False) ∧ (((p1 ∨ p4) ∧ (False ∧ True)) ∨ ((p0 ∨ p0) → (p0 → p2)))) → ((((p0 ∨ p7) → (False → p5)) → ((p2 ∨ p2) → False)) → (((p2 ∧ p0) → (p2 → False)) ∨ ((p0 → True) → (p3 ∧ p0))))) := by
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_6
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        cases assump_11
        case inl assump_13 =>
          cases assump_12
          case intro assump_17 assump_18 =>
            apply False.elim assump_17
        case inr assump_14 =>
          cases assump_12
          case intro assump_23 assump_24 =>
            apply False.elim assump_23
    case inr assump_10 =>
      apply Or.inl
      intro assump_29
      intro assump_30
      cases assump_29
      case intro assump_33 assump_34 =>
        have assump_50 : ((p5 ∧ p6) ∨ (p3 → True)) := by
          apply Or.inr
          intro assump_46
          apply True.intro
        let assump_45 := assump_5 assump_50
        apply False.elim assump_45


variable (p4 p1 p2 p0 : Prop)
theorem file75_12050 : (((((False ∧ p1) → (p0 → p4)) ∨ ((True → False) ∧ (p2 ∨ p1))) → False) → False) := by
  intro assump_1
  have assump_16 : (((False ∧ p1) → (p0 → p4)) ∨ ((True → False) ∧ (p2 ∨ p1))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply False.elim assump_9
  let assump_4 := assump_1 assump_16
  apply False.elim assump_4


variable (p1 p0 p6 p4 p3 : Prop)
theorem file75_12503 : ((((((p3 → False) ∧ (False ∧ p6)) → False) → False) ∧ ((((p6 → False) → False) ∨ ((p0 ∧ p3) ∧ (p4 → p6))) ∧ (((False → False) ∨ (p1 → True)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        have assump_40 : ((False → False) ∨ (p1 → True)) := by
          apply Or.inl
          intro assump_15
          apply False.elim assump_15
        let assump_14 := assump_7 assump_40
        apply False.elim assump_14
      case inr assump_9 =>
        cases assump_9
        case intro assump_21 assump_22 =>
          cases assump_21
          case intro assump_23 assump_24 =>
            have assump_41 : ((False → False) ∨ (p1 → True)) := by
              apply Or.inl
              intro assump_34
              apply False.elim assump_34
            let assump_33 := assump_7 assump_41
            apply False.elim assump_33


variable (p7 p6 p5 p2 p1 p3 : Prop)
theorem file75_13543 : ((((((False → False) ∧ (p7 ∧ p7)) → ((p3 ∧ p2) → (p2 → True))) ∨ (((p5 ∨ p1) → (p6 ∨ p5)) → False)) → False) → False) := by
  intro assump_1
  have assump_11 : ((((False → False) ∧ (p7 ∧ p7)) → ((p3 ∧ p2) → (p2 → True))) ∨ (((p5 ∨ p1) → (p6 ∨ p5)) → False)) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p0 p6 p4 p2 p1 : Prop)
theorem file75_14030 : (((((False ∧ p0) ∧ (p7 ∨ p4)) → False) → False) → ((((p2 ∨ False) → (p6 ∨ True)) ∨ ((p5 → False) → False)) ∨ (((False ∧ p1) ∨ (p2 → p0)) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inl
  intro assump_4
  cases assump_4
  case inl assump_5 =>
    apply Or.inr
    apply True.intro
  case inr assump_6 =>
    apply False.elim assump_6


variable (p0 p7 p6 p3 p4 p2 p1 : Prop)
theorem file75_14442 : (((((p7 → p7) ∧ (p0 → False)) → ((p0 ∧ p3) → (p1 ∨ p7))) ∨ (((p6 ∧ p6) ∧ (p2 → False)) → ((p2 ∨ p2) → False))) ∧ ((((p7 ∨ p3) → (True → False)) ∨ ((True → False) → False)) → (((p2 ∨ p0) → (p2 ∧ p3)) → ((p6 ∨ True) ∨ (False → p4))))) := by
  apply And.intro
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case intro assump_9 assump_10 =>
      have assump_29 : p0 := by
        exact assump_3
      let assump_15 := assump_10 assump_29
      apply False.elim assump_15
  intro assump_19
  intro assump_20
  cases assump_19
  case inl assump_23 =>
    apply Or.inl
    apply Or.inr
    apply True.intro
  case inr assump_24 =>
    apply Or.inl
    apply Or.inr
    apply True.intro


variable (p5 p1 p7 p6 p3 : Prop)
theorem file75_15255 : ((((((p6 ∧ p3) → (True → False)) → False) → (((p5 ∧ False) → False) ∨ ((p6 ∨ p1) → (p6 ∧ p7)))) → False) → False) := by
  intro assump_10
  have assump_27 : ((((p6 ∧ p3) → (True → False)) → False) → (((p5 ∧ False) → False) ∨ ((p6 ∨ p1) → (p6 ∧ p7)))) := by
    intro assump_14
    apply Or.inl
    intro assump_17
    cases assump_17
    case intro assump_18 assump_19 =>
      apply False.elim assump_19
  let assump_13 := assump_10 assump_27
  apply False.elim assump_13


variable (p2 p7 p1 p3 : Prop)
theorem file75_15782 : (((((p7 ∨ p7) ∧ (p1 ∧ False)) → False) → False) → ((((p1 → p3) ∧ (p2 → False)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_32 : (((p7 ∨ p7) ∧ (p1 ∧ False)) → False) := by
    intro assump_8
    cases assump_8
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
  let assump_7 := assump_1 assump_32
  apply False.elim assump_7


variable (p3 p1 p0 p2 p5 p4 p7 : Prop)
theorem file75_16468 : (((((p3 ∧ p3) ∧ (p7 ∧ False)) → ((p5 ∧ p0) ∨ (True ∧ p4))) ∨ (((True ∨ p1) ∧ (p2 ∧ p5)) → ((False ∨ True) → False))) → ((((p1 → False) ∨ (True → False)) → False) → (((p4 ∧ p4) ∧ (False ∧ p7)) → False))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_3
  case intro assump_4 assump_5 =>
    cases assump_4
    case intro assump_6 assump_7 =>
      cases assump_5
      case intro assump_12 assump_13 =>
        apply False.elim assump_12


variable (p7 p6 p1 p5 p4 p3 p0 p2 : Prop)
theorem file75_16996 : (((((p0 ∨ p2) → (p3 ∧ p0)) ∨ ((p6 → p5) ∨ (p3 ∧ True))) → (((p7 ∨ True) ∨ (p2 → p5)) ∨ ((p5 → False) → (p7 ∧ p3)))) ∨ ((((p1 → False) → (p1 ∧ p0)) ∧ ((p3 ∧ p5) → (p7 ∨ True))) → (((p4 → False) → False) → False))) := by
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
      apply Or.inl
      apply Or.inl
      apply Or.inr
      apply True.intro
    case inr assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        apply Or.inl
        apply Or.inr
        apply True.intro


variable (p1 p4 p0 p7 p2 p5 : Prop)
theorem file75_17740 : ((((((p7 ∧ False) ∧ (p4 → False)) → ((p1 ∨ True) ∨ (True → False))) ∨ (((p5 ∧ p0) ∨ (p4 → False)) → ((p2 ∨ p1) ∧ (False ∧ p0)))) → False) → False) := by
  intro assump_1
  have assump_17 : ((((p7 ∧ False) ∧ (p4 → False)) → ((p1 ∨ True) ∨ (True → False))) ∨ (((p5 ∧ p0) ∨ (p4 → False)) → ((p2 ∨ p1) ∧ (False ∧ p0)))) := by
    apply Or.inl
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
  let assump_4 := assump_1 assump_17
  apply False.elim assump_4


variable (p1 p3 p6 p4 p5 p2 p0 : Prop)
theorem file75_18374 : (((((p2 ∧ p4) → (p3 → p4)) ∨ ((p4 → p2) ∨ (p3 → p1))) ∨ (((p5 → p3) → (p0 → p5)) → ((p1 → False) ∧ (p0 → p1)))) ∨ ((((p4 → False) → (True ∧ p3)) ∧ ((p6 ∨ True) ∧ (p3 → False))) → False)) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_12
  intro assump_13
  cases assump_12
  case intro assump_16 assump_17 =>
    exact assump_17


variable (p2 p4 p6 p3 p5 p7 p1 : Prop)
theorem file75_18785 : (((((False → False) ∨ (p5 ∧ True)) ∨ ((p2 → False) → (p3 → False))) ∧ (((p2 ∧ p3) → False) → False)) → ((((p4 ∧ p6) ∧ (p6 ∨ p7)) → ((False ∧ p1) → (p4 → p4))) ∨ (((p6 → False) ∧ (p5 ∧ p2)) ∧ ((True → True) ∧ (p1 ∧ p6))))) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        apply Or.inl
        intro assump_12
        intro assump_13
        intro assump_14
        cases assump_13
        case intro assump_17 assump_18 =>
          apply False.elim assump_17
      case inr assump_7 =>
        cases assump_7
        case intro assump_21 assump_22 =>
          apply Or.inl
          intro assump_29
          intro assump_30
          intro assump_31
          cases assump_30
          case intro assump_34 assump_35 =>
            apply False.elim assump_34
    case inr assump_5 =>
      apply Or.inl
      intro assump_42
      intro assump_43
      intro assump_44
      cases assump_43
      case intro assump_47 assump_48 =>
        apply False.elim assump_47


variable (p4 p5 p7 p6 p0 p3 : Prop)
theorem file75_19938 : (((((False → False) ∧ (p6 → True)) ∨ ((p6 → True) → (True → p4))) → False) → ((((p5 → p3) ∧ (p0 ∨ p7)) ∨ ((True → p0) ∧ (p3 → False))) ∨ (((p4 → p7) → False) → False))) := by
  intro assump_1
  apply Or.inl
  apply Or.inr
  apply And.intro
  intro assump_16
  have assump_39 : (((False → False) ∧ (p6 → True)) ∨ ((p6 → True) → (True → p4))) := by
    apply Or.inl
    apply And.intro
    intro assump_20
    apply False.elim assump_20
    intro assump_23
    apply True.intro
  let assump_19 := assump_1 assump_39
  apply False.elim assump_19
  intro assump_27
  have assump_40 : (((False → False) ∧ (p6 → True)) ∨ ((p6 → True) → (True → p4))) := by
    apply Or.inl
    apply And.intro
    intro assump_32
    apply False.elim assump_32
    intro assump_35
    apply True.intro
  let assump_31 := assump_1 assump_40
  apply False.elim assump_31


variable (p1 p0 p4 p7 p6 p2 : Prop)
theorem file75_20844 : (((((p0 ∨ p2) ∨ (True ∨ p4)) ∨ ((p4 → False) → False)) → False) → ((((True ∧ p7) → False) ∧ ((p4 → p7) → (p7 → False))) ∨ (((p7 ∧ p6) ∧ (p1 ∧ p1)) → False))) := by
  intro assump_1
  apply Or.inl
  apply And.intro
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    have assump_28 : (((p0 ∨ p2) ∨ (True ∨ p4)) ∨ ((p4 → False) → False)) := by
      apply Or.inl
      apply Or.inr
      apply Or.inl
      apply True.intro
    let assump_12 := assump_1 assump_28
    apply False.elim assump_12
  intro assump_16
  intro assump_17
  have assump_29 : (((p0 ∨ p2) ∨ (True ∨ p4)) ∨ ((p4 → False) → False)) := by
    apply Or.inl
    apply Or.inr
    apply Or.inl
    apply True.intro
  let assump_24 := assump_1 assump_29
  apply False.elim assump_24


variable (p1 p3 p2 p6 p0 : Prop)
theorem file75_21667 : (((((p0 → False) → False) → ((p6 → p6) ∨ (p2 → p1))) → (((p6 → p6) ∨ (p3 → False)) → False)) → ((((p3 → False) → (p2 ∨ p0)) → False) → False)) := by
  intro assump_1
  intro assump_2
  have assump_21 : (((p0 → False) → False) → ((p6 → p6) ∨ (p2 → p1))) := by
    intro assump_8
    apply Or.inl
    intro assump_11
    exact assump_11
  let assump_7 := assump_1 assump_21
  have assump_22 : ((p6 → p6) ∨ (p3 → False)) := by
    apply Or.inl
    intro assump_15
    exact assump_15
  let assump_14 := assump_7 assump_22
  apply False.elim assump_14


variable (p4 p2 p7 p5 p1 p3 : Prop)
theorem file75_22275 : (((((p5 ∧ p4) → (False → False)) ∧ ((False → p7) ∨ (True ∨ p5))) ∨ (((p1 → False) ∧ (p5 → False)) ∧ ((p1 → False) ∨ (p3 ∧ p7)))) ∨ ((((p1 ∨ p5) → (p2 → False)) ∨ ((p2 ∧ True) ∧ (p2 ∧ False))) → (((p5 ∧ True) → (True ∧ p1)) → ((p4 → False) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply And.intro
  intro assump_1
  intro assump_2
  apply False.elim assump_2
  apply Or.inl
  intro assump_5
  apply False.elim assump_5


variable (p1 p0 p4 p3 p5 p7 p6 p2 : Prop)
theorem file75_22768 : (((((True ∧ p4) ∧ (p0 ∧ False)) ∧ ((p6 ∨ p2) → (p4 → False))) → False) ∨ ((((True → False) → (p3 → False)) ∧ ((p5 ∨ p2) → False)) → (((p1 ∧ p5) → (p7 ∧ p2)) → ((p1 ∧ p6) ∨ (p1 → p7))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        cases assump_5
        case intro assump_12 assump_13 =>
          apply False.elim assump_13


theorem file75_23283 : ((((((True → False) → False) → False) → False) → False) → False) := by
  intro assump_1
  have assump_22 : ((((True → False) → False) → False) → False) := by
    intro assump_5
    have assump_23 : ((True → False) → False) := by
      intro assump_9
      have assump_24 : True := by
        apply True.intro
      let assump_12 := assump_9 assump_24
      apply False.elim assump_12
    let assump_8 := assump_5 assump_23
    apply False.elim assump_8
  let assump_4 := assump_1 assump_22
  apply False.elim assump_4


variable (p2 p3 p5 p4 p0 p7 : Prop)
theorem file75_23861 : ((((((p5 → p7) ∨ (p4 ∧ p3)) ∨ ((p4 → True) ∨ (p7 ∨ False))) ∨ (((p5 ∨ p3) ∧ (p0 → True)) ∨ ((p7 ∨ True) → False))) ∧ ((((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_4
      case inl assump_6 =>
        cases assump_6
        case inl assump_8 =>
          have assump_121 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
            intro assump_15
            intro assump_16
            intro assump_17
            apply False.elim assump_17
          let assump_14 := assump_3 assump_121
          apply False.elim assump_14
        case inr assump_9 =>
          cases assump_9
          case intro assump_23 assump_24 =>
            have assump_122 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
              intro assump_32
              intro assump_33
              intro assump_34
              apply False.elim assump_34
            let assump_31 := assump_3 assump_122
            apply False.elim assump_31
      case inr assump_7 =>
        cases assump_7
        case inl assump_40 =>
          have assump_123 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
            intro assump_47
            intro assump_48
            intro assump_49
            apply False.elim assump_49
          let assump_46 := assump_3 assump_123
          apply False.elim assump_46
        case inr assump_41 =>
          cases assump_41
          case inl assump_55 =>
            have assump_124 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
              intro assump_62
              intro assump_63
              intro assump_64
              apply False.elim assump_64
            let assump_61 := assump_3 assump_124
            apply False.elim assump_61
          case inr assump_56 =>
            apply False.elim assump_56
    case inr assump_5 =>
      cases assump_5
      case inl assump_72 =>
        cases assump_72
        case intro assump_74 assump_75 =>
          cases assump_74
          case inl assump_76 =>
            have assump_125 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
              intro assump_85
              intro assump_86
              intro assump_87
              apply False.elim assump_87
            let assump_84 := assump_3 assump_125
            apply False.elim assump_84
          case inr assump_77 =>
            have assump_126 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
              intro assump_100
              intro assump_101
              intro assump_102
              apply False.elim assump_102
            let assump_99 := assump_3 assump_126
            apply False.elim assump_99
      case inr assump_73 =>
        have assump_127 : (((p7 → False) ∧ (True ∧ p3)) → ((p3 → False) → (False → p2))) := by
          intro assump_113
          intro assump_114
          intro assump_115
          apply False.elim assump_115
        let assump_112 := assump_3 assump_127
        apply False.elim assump_112


variable (p4 p7 p3 p6 p2 : Prop)
theorem file75_27111 : (((((p3 ∧ p6) → False) → ((p7 ∧ p2) → (p4 ∨ True))) → False) → False) := by
  intro assump_1
  have assump_18 : (((p3 ∧ p6) → False) → ((p7 ∧ p2) → (p4 ∨ True))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case intro assump_7 assump_8 =>
      apply Or.inr
      apply True.intro
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p3 p6 p5 p4 p0 p1 : Prop)
theorem file75_27542 : ((((((p5 ∧ p4) ∨ (p4 → False)) → ((p3 ∨ p1) → False)) → (((p6 → False) ∧ (p0 → p0)) → ((p0 ∧ True) → (p7 ∨ p0)))) → False) → False) := by
  intro assump_6
  have assump_30 : ((((p5 ∧ p4) ∨ (p4 → False)) → ((p3 ∨ p1) → False)) → (((p6 → False) ∧ (p0 → p0)) → ((p0 ∧ True) → (p7 ∨ p0)))) := by
    intro assump_10
    intro assump_11
    intro assump_12
    cases assump_12
    case intro assump_13 assump_14 =>
      cases assump_11
      case intro assump_19 assump_20 =>
        apply Or.inr
        exact assump_13
  let assump_9 := assump_6 assump_30
  apply False.elim assump_9


variable (p1 p0 p2 p5 p4 p3 : Prop)
theorem file75_28184 : (((((p3 ∨ p0) → (p0 → p2)) ∧ ((p3 → False) ∧ (p4 → False))) ∧ (((p1 ∧ p5) ∨ (p5 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        have assump_21 : ((p1 ∧ p5) ∨ (p5 → True)) := by
          apply Or.inr
          intro assump_17
          apply True.intro
        let assump_16 := assump_3 assump_21
        apply False.elim assump_16


variable (p1 p6 p0 p5 p2 p7 p3 p4 : Prop)
theorem file75_28758 : (((((p7 ∧ p7) ∧ (p4 ∧ True)) ∧ ((p4 → False) ∧ (p5 ∨ p1))) ∧ (((p0 → False) → (True → p7)) ∧ ((p1 ∧ p3) ∨ (p7 ∨ p2)))) → ((((False ∨ p3) ∧ (p3 → False)) ∧ ((p1 ∧ p7) ∧ (p6 → p7))) → (((p7 → False) → False) ∨ ((p3 ∨ p3) → False)))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case inl assump_7 =>
        apply False.elim assump_7
      case inr assump_8 =>
        cases assump_4
        case intro assump_15 assump_16 =>
          cases assump_15
          case intro assump_17 assump_18 =>
            cases assump_1
            case intro assump_25 assump_26 =>
              cases assump_25
              case intro assump_27 assump_28 =>
                cases assump_27
                case intro assump_29 assump_30 =>
                  cases assump_29
                  case intro assump_31 assump_32 =>
                    cases assump_30
                    case intro assump_37 assump_38 =>
                      cases assump_28
                      case intro assump_43 assump_44 =>
                        cases assump_44
                        case inl assump_47 =>
                          cases assump_26
                          case intro assump_51 assump_52 =>
                            cases assump_52
                            case inl assump_55 =>
                              cases assump_55
                              case intro assump_57 assump_58 =>
                                apply Or.inl
                                intro assump_63
                                have assump_131 : p7 := by
                                  exact assump_32
                                let assump_66 := assump_63 assump_131
                                apply False.elim assump_66
                            case inr assump_56 =>
                              cases assump_56
                              case inl assump_70 =>
                                apply Or.inl
                                intro assump_74
                                have assump_132 : p7 := by
                                  exact assump_70
                                let assump_77 := assump_74 assump_132
                                apply False.elim assump_77
                              case inr assump_71 =>
                                apply Or.inl
                                intro assump_83
                                have assump_133 : p7 := by
                                  exact assump_32
                                let assump_86 := assump_83 assump_133
                                apply False.elim assump_86
                        case inr assump_48 =>
                          cases assump_26
                          case intro assump_92 assump_93 =>
                            cases assump_93
                            case inl assump_96 =>
                              cases assump_96
                              case intro assump_98 assump_99 =>
                                apply Or.inl
                                intro assump_104
                                have assump_134 : p7 := by
                                  exact assump_32
                                let assump_107 := assump_104 assump_134
                                apply False.elim assump_107
                            case inr assump_97 =>
                              cases assump_97
                              case inl assump_111 =>
                                apply Or.inl
                                intro assump_115
                                have assump_135 : p7 := by
                                  exact assump_111
                                let assump_118 := assump_115 assump_135
                                apply False.elim assump_118
                              case inr assump_112 =>
                                apply Or.inl
                                intro assump_124
                                have assump_136 : p7 := by
                                  exact assump_32
                                let assump_127 := assump_124 assump_136
                                apply False.elim assump_127


variable (p1 p7 p3 p6 p4 p5 p0 : Prop)
theorem file75_33090 : (((((False ∧ p0) → False) ∨ ((p1 → p1) → False)) → (((p0 ∨ p3) → (p4 → p7)) ∨ ((p7 ∨ True) ∧ (p7 → p5)))) → ((((False ∧ p6) ∧ (p0 ∧ p4)) ∧ ((p0 → p7) → (p6 → False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_3
    case intro assump_5 assump_6 =>
      cases assump_5
      case intro assump_7 assump_8 =>
        apply False.elim assump_7


variable (p7 p3 p6 p0 p5 p4 p1 p2 : Prop)
theorem file75_33572 : (((((p4 ∨ p6) ∧ (p1 ∨ p3)) ∧ ((p7 ∨ p5) ∨ (p0 ∧ False))) ∧ (((p1 ∨ p7) ∨ (False → False)) → ((p2 → True) → False))) → False) := by
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
            cases assump_5
            case inl assump_16 =>
              cases assump_16
              case inl assump_18 =>
                have assump_152 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_12
                let assump_24 := assump_3 assump_152
                have assump_153 : (p2 → True) := by
                  intro assump_26
                  apply True.intro
                let assump_25 := assump_24 assump_153
                apply False.elim assump_25
              case inr assump_19 =>
                have assump_154 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_12
                let assump_34 := assump_3 assump_154
                have assump_155 : (p2 → True) := by
                  intro assump_36
                  apply True.intro
                let assump_35 := assump_34 assump_155
                apply False.elim assump_35
            case inr assump_17 =>
              cases assump_17
              case intro assump_40 assump_41 =>
                apply False.elim assump_41
          case inr assump_13 =>
            cases assump_5
            case inl assump_48 =>
              cases assump_48
              case inl assump_50 =>
                have assump_156 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_50
                let assump_56 := assump_3 assump_156
                have assump_157 : (p2 → True) := by
                  intro assump_58
                  apply True.intro
                let assump_57 := assump_56 assump_157
                apply False.elim assump_57
              case inr assump_51 =>
                have assump_158 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inr
                  intro assump_67
                  apply False.elim assump_67
                let assump_66 := assump_3 assump_158
                have assump_159 : (p2 → True) := by
                  intro assump_71
                  apply True.intro
                let assump_70 := assump_66 assump_159
                apply False.elim assump_70
            case inr assump_49 =>
              cases assump_49
              case intro assump_75 assump_76 =>
                apply False.elim assump_76
        case inr assump_9 =>
          cases assump_7
          case inl assump_83 =>
            cases assump_5
            case inl assump_87 =>
              cases assump_87
              case inl assump_89 =>
                have assump_160 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_83
                let assump_95 := assump_3 assump_160
                have assump_161 : (p2 → True) := by
                  intro assump_97
                  apply True.intro
                let assump_96 := assump_95 assump_161
                apply False.elim assump_96
              case inr assump_90 =>
                have assump_162 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inl
                  apply Or.inl
                  exact assump_83
                let assump_105 := assump_3 assump_162
                have assump_163 : (p2 → True) := by
                  intro assump_107
                  apply True.intro
                let assump_106 := assump_105 assump_163
                apply False.elim assump_106
            case inr assump_88 =>
              cases assump_88
              case intro assump_111 assump_112 =>
                apply False.elim assump_112
          case inr assump_84 =>
            cases assump_5
            case inl assump_119 =>
              cases assump_119
              case inl assump_121 =>
                have assump_164 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inl
                  apply Or.inr
                  exact assump_121
                let assump_127 := assump_3 assump_164
                have assump_165 : (p2 → True) := by
                  intro assump_129
                  apply True.intro
                let assump_128 := assump_127 assump_165
                apply False.elim assump_128
              case inr assump_122 =>
                have assump_166 : ((p1 ∨ p7) ∨ (False → False)) := by
                  apply Or.inr
                  intro assump_138
                  apply False.elim assump_138
                let assump_137 := assump_3 assump_166
                have assump_167 : (p2 → True) := by
                  intro assump_142
                  apply True.intro
                let assump_141 := assump_137 assump_167
                apply False.elim assump_141
            case inr assump_120 =>
              cases assump_120
              case intro assump_146 assump_147 =>
                apply False.elim assump_147


variable (p5 : Prop)
theorem file75_39015 : ((((((False → False) ∨ (True ∨ p5)) → False) → False) → False) → False) := by
  intro assump_1
  have assump_18 : ((((False → False) ∨ (True ∨ p5)) → False) → False) := by
    intro assump_5
    have assump_19 : ((False → False) ∨ (True ∨ p5)) := by
      apply Or.inl
      intro assump_9
      apply False.elim assump_9
    let assump_8 := assump_5 assump_19
    apply False.elim assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4


variable (p7 p0 p3 p6 p5 : Prop)
theorem file75_39528 : (((((p6 ∧ False) ∧ (p3 → False)) → False) → (((p6 ∨ p3) → False) ∧ ((p6 ∧ True) ∨ (True → False)))) → ((((p0 ∧ p6) → False) → ((p7 → False) ∧ (p7 ∨ p0))) ∨ (((False → False) → False) ∨ ((p7 ∨ p5) → False)))) := by
  intro assump_1
  apply Or.inl
  intro assump_4
  apply And.intro
  intro assump_5
  have assump_104 : (((p6 ∧ False) ∧ (p3 → False)) → False) := by
    intro assump_13
    cases assump_13
    case intro assump_14 assump_15 =>
      cases assump_14
      case intro assump_16 assump_17 =>
        apply False.elim assump_17
  let assump_12 := assump_1 assump_104
  let assump_22 := And.right assump_12
  cases assump_22
  case inl assump_25 =>
    cases assump_25
    case intro assump_27 assump_28 =>
      have assump_105 : (((p6 ∧ False) ∧ (p3 → False)) → False) := by
        intro assump_37
        cases assump_37
        case intro assump_38 assump_39 =>
          cases assump_38
          case intro assump_40 assump_41 =>
            apply False.elim assump_41
      let assump_36 := assump_1 assump_105
      let assump_46 := And.left assump_36
      have assump_106 : (p6 ∨ p3) := by
        apply Or.inl
        exact assump_27
      let assump_47 := assump_46 assump_106
      apply False.elim assump_47
  case inr assump_26 =>
    have assump_107 : True := by
      apply True.intro
    let assump_53 := assump_26 assump_107
    apply False.elim assump_53
  have assump_108 : (((p6 ∧ False) ∧ (p3 → False)) → False) := by
    intro assump_61
    cases assump_61
    case intro assump_62 assump_63 =>
      cases assump_62
      case intro assump_64 assump_65 =>
        apply False.elim assump_65
  let assump_60 := assump_1 assump_108
  let assump_70 := And.right assump_60
  cases assump_70
  case inl assump_73 =>
    cases assump_73
    case intro assump_75 assump_76 =>
      have assump_109 : (((p6 ∧ False) ∧ (p3 → False)) → False) := by
        intro assump_84
        cases assump_84
        case intro assump_85 assump_86 =>
          cases assump_85
          case intro assump_87 assump_88 =>
            apply False.elim assump_88
      let assump_83 := assump_1 assump_109
      let assump_93 := And.left assump_83
      have assump_110 : (p6 ∨ p3) := by
        apply Or.inl
        exact assump_75
      let assump_94 := assump_93 assump_110
      apply False.elim assump_94
  case inr assump_74 =>
    have assump_111 : True := by
      apply True.intro
    let assump_100 := assump_74 assump_111
    apply False.elim assump_100


variable (p4 p0 p3 p2 p7 p1 : Prop)
theorem file75_42064 : ((((((p3 ∧ p1) ∨ (True → False)) → False) → (((p7 → True) ∨ (p0 ∨ p2)) ∨ ((False ∨ p4) → (p0 → False)))) → False) → False) := by
  intro assump_21
  have assump_32 : ((((p3 ∧ p1) ∨ (True → False)) → False) → (((p7 → True) ∨ (p0 ∨ p2)) ∨ ((False ∨ p4) → (p0 → False)))) := by
    intro assump_25
    apply Or.inl
    apply Or.inl
    intro assump_28
    apply True.intro
  let assump_24 := assump_21 assump_32
  apply False.elim assump_24


variable (p7 p1 p5 p4 p3 p2 p0 : Prop)
theorem file75_42565 : ((((((p3 → True) ∧ (True → False)) → ((p4 → False) ∨ (False → False))) ∧ (((p5 ∧ p1) → (p7 ∨ p3)) ∧ ((p3 → False) ∨ (False → False)))) ∧ ((((p7 → True) → False) → ((p7 ∨ p7) ∧ (p2 ∧ p0))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_5
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_74 : (((p7 → True) → False) → ((p7 ∨ p7) ∧ (p2 ∧ p0))) := by
            intro assump_19
            apply And.intro
            have assump_75 : (p7 → True) := by
              intro assump_23
              apply True.intro
            let assump_22 := assump_19 assump_75
            apply False.elim assump_22
            apply And.intro
            have assump_76 : (p7 → True) := by
              intro assump_30
              apply True.intro
            let assump_29 := assump_19 assump_76
            apply False.elim assump_29
            have assump_77 : (p7 → True) := by
              intro assump_37
              apply True.intro
            let assump_36 := assump_19 assump_77
            apply False.elim assump_36
          let assump_18 := assump_3 assump_74
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_78 : (((p7 → True) → False) → ((p7 ∨ p7) ∧ (p2 ∧ p0))) := by
            intro assump_49
            apply And.intro
            have assump_79 : (p7 → True) := by
              intro assump_53
              apply True.intro
            let assump_52 := assump_49 assump_79
            apply False.elim assump_52
            apply And.intro
            have assump_80 : (p7 → True) := by
              intro assump_60
              apply True.intro
            let assump_59 := assump_49 assump_80
            apply False.elim assump_59
            have assump_81 : (p7 → True) := by
              intro assump_67
              apply True.intro
            let assump_66 := assump_49 assump_81
            apply False.elim assump_66
          let assump_48 := assump_3 assump_78
          apply False.elim assump_48


variable (p4 p2 p3 p0 p5 p6 : Prop)
theorem file75_44779 : (((((p2 ∧ False) ∧ (p2 → p2)) ∧ ((p4 → p3) ∨ (p5 → False))) → False) ∨ ((((False ∨ p3) → (p3 ∨ p0)) → ((p0 → p3) ∧ (False ∨ p6))) ∧ (((p5 ∧ p0) ∨ (False ∨ p0)) ∧ ((p2 → p4) → (p3 → p5))))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case intro assump_4 assump_5 =>
      cases assump_4
      case intro assump_6 assump_7 =>
        apply False.elim assump_7


variable (p3 p5 p7 p2 p0 p6 : Prop)
theorem file75_45265 : ((((((p6 ∨ p7) → (False → False)) ∨ ((p0 ∧ True) ∨ (p7 ∨ p5))) → False) ∨ ((((p5 → False) → (p2 ∨ False)) → ((True ∨ True) ∨ (p2 ∨ p3))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_23 : (((p6 ∨ p7) → (False → False)) ∨ ((p0 ∧ True) ∨ (p7 ∨ p5))) := by
      apply Or.inl
      intro assump_7
      intro assump_8
      apply False.elim assump_8
    let assump_6 := assump_2 assump_23
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_24 : (((p5 → False) → (p2 ∨ False)) → ((True ∨ True) ∨ (p2 ∨ p3))) := by
      intro assump_17
      apply Or.inl
      apply Or.inl
      apply True.intro
    let assump_16 := assump_3 assump_24
    apply False.elim assump_16


variable (p3 p5 p4 p7 : Prop)
theorem file75_46053 : ((((((p5 → True) → False) → ((p4 → False) ∨ (p7 → p3))) ∨ (((True ∨ p7) → (p5 ∨ True)) ∨ ((p5 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_20 : ((((p5 → True) → False) → ((p4 → False) ∨ (p7 → p3))) ∨ (((True ∨ p7) → (p5 ∨ True)) ∨ ((p5 → False) → False))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    have assump_21 : (p5 → True) := by
      intro assump_13
      apply True.intro
    let assump_12 := assump_5 assump_21
    apply False.elim assump_12
  let assump_4 := assump_1 assump_20
  apply False.elim assump_4


variable (p7 p4 p5 p1 p0 p6 p3 p2 : Prop)
theorem file75_46703 : ((((((p5 → False) ∧ (True → False)) → ((p3 ∨ p2) ∨ (p7 → p6))) → False) ∧ ((((p2 ∧ True) ∨ (p7 ∨ p7)) ∧ ((False → p5) ∨ (True ∨ p2))) → (((p4 ∨ p0) ∨ (p6 → False)) → ((p6 → p7) → (p1 ∨ p4))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_28 : (((p5 → False) ∧ (True → False)) → ((p3 ∨ p2) ∨ (p7 → p6))) := by
      intro assump_10
      cases assump_10
      case intro assump_11 assump_12 =>
        apply Or.inr
        intro assump_17
        have assump_29 : True := by
          apply True.intro
        let assump_21 := assump_12 assump_29
        apply False.elim assump_21
    let assump_9 := assump_2 assump_28
    apply False.elim assump_9


variable (p1 p0 p2 p7 p4 : Prop)
theorem file75_47464 : ((((((p2 ∨ p2) → (False → p4)) ∨ ((False ∨ p7) ∨ (p4 → p1))) ∨ (((p7 ∨ p0) ∧ (True ∨ True)) ∧ ((p2 ∨ p0) → False))) → False) → False) := by
  intro assump_8
  have assump_19 : ((((p2 ∨ p2) → (False → p4)) ∨ ((False ∨ p7) ∨ (p4 → p1))) ∨ (((p7 ∨ p0) ∧ (True ∨ True)) ∧ ((p2 ∨ p0) → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_12
    intro assump_13
    apply False.elim assump_13
  let assump_11 := assump_8 assump_19
  apply False.elim assump_11


variable (p0 p5 p1 p3 p4 p6 p2 : Prop)
theorem file75_47995 : ((((((p6 → False) ∧ (p2 ∨ False)) ∧ ((p6 → p1) → (p3 → p1))) ∧ (((p0 → False) → False) ∨ ((p1 ∧ p6) → False))) ∧ ((((p1 → False) ∧ (p3 → p5)) ∨ ((p0 → p2) → (p1 ∧ p3))) ∧ (((p6 ∧ p4) ∨ (False ∧ p6)) ∧ ((p2 ∧ p5) ∧ (p0 ∧ False))))) → False) := by
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
            cases assump_5
            case inl assump_18 =>
              cases assump_3
              case intro assump_22 assump_23 =>
                cases assump_22
                case inl assump_24 =>
                  cases assump_24
                  case intro assump_26 assump_27 =>
                    cases assump_23
                    case intro assump_32 assump_33 =>
                      cases assump_32
                      case inl assump_34 =>
                        cases assump_34
                        case intro assump_36 assump_37 =>
                          cases assump_33
                          case intro assump_42 assump_43 =>
                            cases assump_42
                            case intro assump_44 assump_45 =>
                              cases assump_43
                              case intro assump_50 assump_51 =>
                                apply False.elim assump_51
                      case inr assump_35 =>
                        cases assump_35
                        case intro assump_56 assump_57 =>
                          apply False.elim assump_56
                case inr assump_25 =>
                  cases assump_23
                  case intro assump_62 assump_63 =>
                    cases assump_62
                    case inl assump_64 =>
                      cases assump_64
                      case intro assump_66 assump_67 =>
                        cases assump_63
                        case intro assump_72 assump_73 =>
                          cases assump_72
                          case intro assump_74 assump_75 =>
                            cases assump_73
                            case intro assump_80 assump_81 =>
                              apply False.elim assump_81
                    case inr assump_65 =>
                      cases assump_65
                      case intro assump_86 assump_87 =>
                        apply False.elim assump_86
            case inr assump_19 =>
              cases assump_3
              case intro assump_92 assump_93 =>
                cases assump_92
                case inl assump_94 =>
                  cases assump_94
                  case intro assump_96 assump_97 =>
                    cases assump_93
                    case intro assump_102 assump_103 =>
                      cases assump_102
                      case inl assump_104 =>
                        cases assump_104
                        case intro assump_106 assump_107 =>
                          cases assump_103
                          case intro assump_112 assump_113 =>
                            cases assump_112
                            case intro assump_114 assump_115 =>
                              cases assump_113
                              case intro assump_120 assump_121 =>
                                apply False.elim assump_121
                      case inr assump_105 =>
                        cases assump_105
                        case intro assump_126 assump_127 =>
                          apply False.elim assump_126
                case inr assump_95 =>
                  cases assump_93
                  case intro assump_132 assump_133 =>
                    cases assump_132
                    case inl assump_134 =>
                      cases assump_134
                      case intro assump_136 assump_137 =>
                        cases assump_133
                        case intro assump_142 assump_143 =>
                          cases assump_142
                          case intro assump_144 assump_145 =>
                            cases assump_143
                            case intro assump_150 assump_151 =>
                              apply False.elim assump_151
                    case inr assump_135 =>
                      cases assump_135
                      case intro assump_156 assump_157 =>
                        apply False.elim assump_156
          case inr assump_13 =>
            apply False.elim assump_13


variable (p0 p4 p1 p7 p6 : Prop)
theorem file75_52652 : (((((p6 → False) ∧ (p0 → p0)) → ((p7 → p1) ∧ (p1 ∧ p4))) ∧ (((p4 ∧ True) ∨ (p4 → True)) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_13 : ((p4 ∧ True) ∨ (p4 → True)) := by
      apply Or.inr
      intro assump_9
      apply True.intro
    let assump_8 := assump_3 assump_13
    apply False.elim assump_8


variable (p6 p3 p5 p4 : Prop)
theorem file75_53074 : ((((((p3 → False) ∧ (True → False)) ∧ ((True ∨ False) → (p3 → False))) → (((True ∨ p6) → (False → False)) → ((p6 → p5) → (p4 → p6)))) → False) → False) := by
  intro assump_1
  have assump_34 : ((((p3 → False) ∧ (True → False)) ∧ ((True ∨ False) → (p3 → False))) → (((True ∨ p6) → (False → False)) → ((p6 → p5) → (p4 → p6)))) := by
    intro assump_5
    intro assump_6
    intro assump_7
    intro assump_8
    cases assump_5
    case intro assump_15 assump_16 =>
      cases assump_15
      case intro assump_17 assump_18 =>
        have assump_35 : True := by
          apply True.intro
        let assump_27 := assump_18 assump_35
        apply False.elim assump_27
  let assump_4 := assump_1 assump_34
  apply False.elim assump_4


variable (p0 p5 : Prop)
theorem file75_53857 : ((((((p0 ∨ True) → False) ∨ ((p5 → p5) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p0 ∨ True) → False) ∨ ((p5 → p5) → False)) → False) := by
    intro assump_5
    cases assump_5
    case inl assump_6 =>
      have assump_27 : (p0 ∨ True) := by
        apply Or.inr
        apply True.intro
      let assump_10 := assump_6 assump_27
      apply False.elim assump_10
    case inr assump_7 =>
      have assump_28 : (p5 → p5) := by
        intro assump_17
        exact assump_17
      let assump_16 := assump_7 assump_28
      apply False.elim assump_16
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p5 p3 p7 p2 p0 p1 p6 : Prop)
theorem file75_54577 : (((((p0 → False) ∨ (p3 ∧ p0)) → False) → (((True ∨ p1) ∨ (p5 → p5)) ∨ ((p1 → False) ∧ (p2 ∧ p6)))) ∨ ((((True → p5) ∧ (False ∨ p0)) ∧ ((p6 → False) ∨ (False ∨ p7))) → False)) := by
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply True.intro


variable (p2 p6 p1 p3 p5 p0 p4 p7 : Prop)
theorem file75_54920 : (((((p7 ∨ p2) → False) ∧ ((p7 → p0) ∨ (p6 ∧ p4))) → (((p3 → False) ∧ (p2 ∧ p6)) → False)) ∨ ((((p5 ∨ False) ∨ (p3 → p5)) ∨ ((True ∨ p1) → False)) → (((False → False) → (p2 → p0)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_4
    case intro assump_7 assump_8 =>
      cases assump_1
      case intro assump_13 assump_14 =>
        cases assump_14
        case inl assump_17 =>
          have assump_38 : (p7 ∨ p2) := by
            apply Or.inr
            exact assump_7
          let assump_22 := assump_13 assump_38
          apply False.elim assump_22
        case inr assump_18 =>
          cases assump_18
          case intro assump_26 assump_27 =>
            have assump_39 : (p7 ∨ p2) := by
              apply Or.inr
              exact assump_7
            let assump_34 := assump_13 assump_39
            apply False.elim assump_34


variable (p5 p3 p7 p6 p1 p4 : Prop)
theorem file75_55914 : ((((((p3 ∧ True) → False) → ((p1 → True) ∨ (p4 → False))) ∨ (((p5 ∨ p3) → (p7 → p6)) → False)) → False) → False) := by
  intro assump_1
  have assump_12 : ((((p3 ∧ True) → False) → ((p1 → True) ∨ (p4 → False))) ∨ (((p5 ∨ p3) → (p7 → p6)) → False)) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    apply True.intro
  let assump_4 := assump_1 assump_12
  apply False.elim assump_4


variable (p6 p7 p0 p5 p3 p4 p1 p2 : Prop)
theorem file75_56392 : ((((((True ∨ p1) ∨ (p3 ∨ p5)) → ((p5 → p5) ∨ (p4 → p0))) ∨ (((p4 → False) → (True ∨ p0)) ∨ ((p0 ∨ p6) ∧ (p4 → False)))) ∧ ((((p7 → p0) ∨ (p3 → p6)) ∨ ((p7 → p4) ∨ (True ∨ p5))) ∧ (((p1 ∨ False) ∧ (p1 → False)) ∧ ((p1 ∧ p1) → (p3 → p2))))) → False) := by
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
            cases assump_9
            case intro assump_16 assump_17 =>
              cases assump_16
              case intro assump_18 assump_19 =>
                cases assump_18
                case inl assump_20 =>
                  have assump_504 : p1 := by
                    exact assump_20
                  let assump_30 := assump_19 assump_504
                  apply False.elim assump_30
                case inr assump_21 =>
                  apply False.elim assump_21
          case inr assump_13 =>
            cases assump_9
            case intro assump_38 assump_39 =>
              cases assump_38
              case intro assump_40 assump_41 =>
                cases assump_40
                case inl assump_42 =>
                  have assump_505 : p1 := by
                    exact assump_42
                  let assump_52 := assump_41 assump_505
                  apply False.elim assump_52
                case inr assump_43 =>
                  apply False.elim assump_43
        case inr assump_11 =>
          cases assump_11
          case inl assump_58 =>
            cases assump_9
            case intro assump_62 assump_63 =>
              cases assump_62
              case intro assump_64 assump_65 =>
                cases assump_64
                case inl assump_66 =>
                  have assump_506 : p1 := by
                    exact assump_66
                  let assump_76 := assump_65 assump_506
                  apply False.elim assump_76
                case inr assump_67 =>
                  apply False.elim assump_67
          case inr assump_59 =>
            cases assump_59
            case inl assump_82 =>
              cases assump_9
              case intro assump_86 assump_87 =>
                cases assump_86
                case intro assump_88 assump_89 =>
                  cases assump_88
                  case inl assump_90 =>
                    have assump_507 : p1 := by
                      exact assump_90
                    let assump_100 := assump_89 assump_507
                    apply False.elim assump_100
                  case inr assump_91 =>
                    apply False.elim assump_91
            case inr assump_83 =>
              cases assump_9
              case intro assump_108 assump_109 =>
                cases assump_108
                case intro assump_110 assump_111 =>
                  cases assump_110
                  case inl assump_112 =>
                    have assump_508 : p1 := by
                      exact assump_112
                    let assump_122 := assump_111 assump_508
                    apply False.elim assump_122
                  case inr assump_113 =>
                    apply False.elim assump_113
    case inr assump_5 =>
      cases assump_5
      case inl assump_128 =>
        cases assump_3
        case intro assump_132 assump_133 =>
          cases assump_132
          case inl assump_134 =>
            cases assump_134
            case inl assump_136 =>
              cases assump_133
              case intro assump_140 assump_141 =>
                cases assump_140
                case intro assump_142 assump_143 =>
                  cases assump_142
                  case inl assump_144 =>
                    have assump_509 : p1 := by
                      exact assump_144
                    let assump_154 := assump_143 assump_509
                    apply False.elim assump_154
                  case inr assump_145 =>
                    apply False.elim assump_145
            case inr assump_137 =>
              cases assump_133
              case intro assump_162 assump_163 =>
                cases assump_162
                case intro assump_164 assump_165 =>
                  cases assump_164
                  case inl assump_166 =>
                    have assump_510 : p1 := by
                      exact assump_166
                    let assump_176 := assump_165 assump_510
                    apply False.elim assump_176
                  case inr assump_167 =>
                    apply False.elim assump_167
          case inr assump_135 =>
            cases assump_135
            case inl assump_182 =>
              cases assump_133
              case intro assump_186 assump_187 =>
                cases assump_186
                case intro assump_188 assump_189 =>
                  cases assump_188
                  case inl assump_190 =>
                    have assump_511 : p1 := by
                      exact assump_190
                    let assump_200 := assump_189 assump_511
                    apply False.elim assump_200
                  case inr assump_191 =>
                    apply False.elim assump_191
            case inr assump_183 =>
              cases assump_183
              case inl assump_206 =>
                cases assump_133
                case intro assump_210 assump_211 =>
                  cases assump_210
                  case intro assump_212 assump_213 =>
                    cases assump_212
                    case inl assump_214 =>
                      have assump_512 : p1 := by
                        exact assump_214
                      let assump_224 := assump_213 assump_512
                      apply False.elim assump_224
                    case inr assump_215 =>
                      apply False.elim assump_215
              case inr assump_207 =>
                cases assump_133
                case intro assump_232 assump_233 =>
                  cases assump_232
                  case intro assump_234 assump_235 =>
                    cases assump_234
                    case inl assump_236 =>
                      have assump_513 : p1 := by
                        exact assump_236
                      let assump_246 := assump_235 assump_513
                      apply False.elim assump_246
                    case inr assump_237 =>
                      apply False.elim assump_237
      case inr assump_129 =>
        cases assump_129
        case intro assump_252 assump_253 =>
          cases assump_252
          case inl assump_254 =>
            cases assump_3
            case intro assump_260 assump_261 =>
              cases assump_260
              case inl assump_262 =>
                cases assump_262
                case inl assump_264 =>
                  cases assump_261
                  case intro assump_268 assump_269 =>
                    cases assump_268
                    case intro assump_270 assump_271 =>
                      cases assump_270
                      case inl assump_272 =>
                        have assump_514 : p1 := by
                          exact assump_272
                        let assump_282 := assump_271 assump_514
                        apply False.elim assump_282
                      case inr assump_273 =>
                        apply False.elim assump_273
                case inr assump_265 =>
                  cases assump_261
                  case intro assump_290 assump_291 =>
                    cases assump_290
                    case intro assump_292 assump_293 =>
                      cases assump_292
                      case inl assump_294 =>
                        have assump_515 : p1 := by
                          exact assump_294
                        let assump_304 := assump_293 assump_515
                        apply False.elim assump_304
                      case inr assump_295 =>
                        apply False.elim assump_295
              case inr assump_263 =>
                cases assump_263
                case inl assump_310 =>
                  cases assump_261
                  case intro assump_314 assump_315 =>
                    cases assump_314
                    case intro assump_316 assump_317 =>
                      cases assump_316
                      case inl assump_318 =>
                        have assump_516 : p1 := by
                          exact assump_318
                        let assump_328 := assump_317 assump_516
                        apply False.elim assump_328
                      case inr assump_319 =>
                        apply False.elim assump_319
                case inr assump_311 =>
                  cases assump_311
                  case inl assump_334 =>
                    cases assump_261
                    case intro assump_338 assump_339 =>
                      cases assump_338
                      case intro assump_340 assump_341 =>
                        cases assump_340
                        case inl assump_342 =>
                          have assump_517 : p1 := by
                            exact assump_342
                          let assump_352 := assump_341 assump_517
                          apply False.elim assump_352
                        case inr assump_343 =>
                          apply False.elim assump_343
                  case inr assump_335 =>
                    cases assump_261
                    case intro assump_360 assump_361 =>
                      cases assump_360
                      case intro assump_362 assump_363 =>
                        cases assump_362
                        case inl assump_364 =>
                          have assump_518 : p1 := by
                            exact assump_364
                          let assump_374 := assump_363 assump_518
                          apply False.elim assump_374
                        case inr assump_365 =>
                          apply False.elim assump_365
          case inr assump_255 =>
            cases assump_3
            case intro assump_384 assump_385 =>
              cases assump_384
              case inl assump_386 =>
                cases assump_386
                case inl assump_388 =>
                  cases assump_385
                  case intro assump_392 assump_393 =>
                    cases assump_392
                    case intro assump_394 assump_395 =>
                      cases assump_394
                      case inl assump_396 =>
                        have assump_519 : p1 := by
                          exact assump_396
                        let assump_406 := assump_395 assump_519
                        apply False.elim assump_406
                      case inr assump_397 =>
                        apply False.elim assump_397
                case inr assump_389 =>
                  cases assump_385
                  case intro assump_414 assump_415 =>
                    cases assump_414
                    case intro assump_416 assump_417 =>
                      cases assump_416
                      case inl assump_418 =>
                        have assump_520 : p1 := by
                          exact assump_418
                        let assump_428 := assump_417 assump_520
                        apply False.elim assump_428
                      case inr assump_419 =>
                        apply False.elim assump_419
              case inr assump_387 =>
                cases assump_387
                case inl assump_434 =>
                  cases assump_385
                  case intro assump_438 assump_439 =>
                    cases assump_438
                    case intro assump_440 assump_441 =>
                      cases assump_440
                      case inl assump_442 =>
                        have assump_521 : p1 := by
                          exact assump_442
                        let assump_452 := assump_441 assump_521
                        apply False.elim assump_452
                      case inr assump_443 =>
                        apply False.elim assump_443
                case inr assump_435 =>
                  cases assump_435
                  case inl assump_458 =>
                    cases assump_385
                    case intro assump_462 assump_463 =>
                      cases assump_462
                      case intro assump_464 assump_465 =>
                        cases assump_464
                        case inl assump_466 =>
                          have assump_522 : p1 := by
                            exact assump_466
                          let assump_476 := assump_465 assump_522
                          apply False.elim assump_476
                        case inr assump_467 =>
                          apply False.elim assump_467
                  case inr assump_459 =>
                    cases assump_385
                    case intro assump_484 assump_485 =>
                      cases assump_484
                      case intro assump_486 assump_487 =>
                        cases assump_486
                        case inl assump_488 =>
                          have assump_523 : p1 := by
                            exact assump_488
                          let assump_498 := assump_487 assump_523
                          apply False.elim assump_498
                        case inr assump_489 =>
                          apply False.elim assump_489


variable (p4 p0 p2 p5 p3 p7 : Prop)
theorem file75_69995 : (((((p3 ∨ p0) → False) ∧ ((True → False) ∧ (p3 ∧ p3))) → (((False ∨ p2) → (p3 → False)) ∨ ((p5 ∨ p4) ∧ (p0 ∧ p7)))) ∨ ((((False ∨ True) → False) ∨ ((p7 → True) ∨ (p4 ∧ p0))) → (((p7 ∧ False) → False) ∧ ((p5 → True) → False)))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        apply Or.inl
        intro assump_16
        intro assump_17
        cases assump_16
        case inl assump_20 =>
          apply False.elim assump_20
        case inr assump_21 =>
          have assump_34 : True := by
            apply True.intro
          let assump_30 := assump_6 assump_34
          apply False.elim assump_30


variable (p3 p7 p6 p1 p5 p2 p0 p4 : Prop)
theorem file75_70833 : (((((p4 ∧ p1) ∨ (p7 ∧ p3)) ∨ ((p3 → p2) → (True ∨ p0))) ∧ (((True ∨ True) → False) → False)) ∨ ((((p7 ∧ True) ∨ (p0 ∧ p2)) ∨ ((p5 → False) → (p7 → False))) → (((p0 ∨ p6) → (p0 → p4)) ∨ ((p3 → False) ∨ (p2 → False))))) := by
  apply Or.inl
  apply And.intro
  apply Or.inr
  intro assump_1
  apply Or.inl
  apply True.intro
  intro assump_4
  have assump_11 : (True ∨ True) := by
    apply Or.inl
    apply True.intro
  let assump_7 := assump_4 assump_11
  apply False.elim assump_7


variable (p5 p0 p4 p3 : Prop)
theorem file75_71369 : ((((((True → False) ∧ (p0 → False)) → False) ∨ (((p5 → p3) → False) → ((p3 → p5) ∨ (p4 ∧ p4)))) → False) → False) := by
  intro assump_14
  have assump_33 : ((((True → False) ∧ (p0 → False)) → False) ∨ (((p5 → p3) → False) → ((p3 → p5) ∨ (p4 ∧ p4)))) := by
    apply Or.inl
    intro assump_18
    cases assump_18
    case intro assump_19 assump_20 =>
      have assump_34 : True := by
        apply True.intro
      let assump_26 := assump_19 assump_34
      apply False.elim assump_26
  let assump_17 := assump_14 assump_33
  apply False.elim assump_17


variable (p6 p2 p4 p0 p3 : Prop)
theorem file75_71981 : ((((((p6 ∧ p2) ∨ (p6 ∨ p0)) → ((p0 → False) → False)) → (((True ∨ p3) ∨ (p2 ∨ p4)) ∨ ((p3 → False) → False))) → False) → False) := by
  intro assump_1
  have assump_11 : ((((p6 ∧ p2) ∨ (p6 ∨ p0)) → ((p0 → False) → False)) → (((True ∨ p3) ∨ (p2 ∨ p4)) ∨ ((p3 → False) → False))) := by
    intro assump_5
    apply Or.inl
    apply Or.inl
    apply Or.inl
    apply True.intro
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p1 p4 p3 p7 p2 p6 : Prop)
theorem file75_72481 : (((((p7 ∨ True) → False) ∧ ((p1 ∨ p3) → False)) → (((p6 ∨ False) → (p1 ∧ p3)) → False)) ∨ ((((p2 → p4) ∨ (p4 → False)) ∨ ((True → p7) → False)) → False)) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    have assump_16 : (p7 ∨ True) := by
      apply Or.inr
      apply True.intro
    let assump_12 := assump_5 assump_16
    apply False.elim assump_12


variable (p5 p4 p2 p7 p1 p0 p6 : Prop)
theorem file75_72956 : ((((((p0 ∧ False) ∧ (p0 → False)) ∧ ((False → False) → False)) ∧ (((p2 ∨ p5) ∨ (p1 → False)) ∧ ((p4 ∧ p7) ∧ (p1 ∨ p2)))) ∧ ((((p7 → False) → (p6 → p0)) ∧ ((p6 → False) ∨ (p5 → False))) → False)) → False) := by
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
            apply False.elim assump_11


variable (p2 p7 p6 p0 p1 p4 : Prop)
theorem file75_73579 : (((((p4 ∧ p2) ∧ (False → True)) ∧ ((p7 ∨ True) → (True → False))) → False) ∨ ((((p6 ∨ True) → False) → ((False → False) ∧ (p0 ∧ False))) → (((True → p1) ∨ (True ∨ p7)) → ((p6 → p2) → (False → p4))))) := by
  apply Or.inl
  intro assump_18
  cases assump_18
  case intro assump_19 assump_20 =>
    cases assump_19
    case intro assump_21 assump_22 =>
      cases assump_21
      case intro assump_23 assump_24 =>
        have assump_38 : (p7 ∨ True) := by
          apply Or.inr
          apply True.intro
        let assump_33 := assump_20 assump_38
        have assump_39 : True := by
          apply True.intro
        let assump_34 := assump_33 assump_39
        apply False.elim assump_34


variable (p2 p0 p7 p1 p4 p6 p3 p5 : Prop)
theorem file75_74339 : (((((True ∨ p2) ∧ (p5 ∨ p4)) ∧ ((False ∨ p2) ∨ (p2 → p6))) ∧ (((p4 → False) → False) ∧ ((p6 → False) ∨ (p0 → False)))) → ((((p5 → False) ∧ (p1 ∨ p7)) → ((p5 ∨ p6) → (p5 → False))) ∨ (((p7 → True) ∧ (p3 → False)) ∧ ((True ∨ True) ∨ (p7 ∨ p3))))) := by
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
            cases assump_5
            case inl assump_16 =>
              cases assump_16
              case inl assump_18 =>
                apply False.elim assump_18
              case inr assump_19 =>
                cases assump_3
                case intro assump_24 assump_25 =>
                  cases assump_25
                  case inl assump_28 =>
                    apply Or.inl
                    intro assump_32
                    intro assump_33
                    intro assump_34
                    cases assump_33
                    case inl assump_37 =>
                      cases assump_32
                      case intro assump_41 assump_42 =>
                        cases assump_42
                        case inl assump_45 =>
                          have assump_962 : p5 := by
                            exact assump_37
                          let assump_50 := assump_41 assump_962
                          apply False.elim assump_50
                        case inr assump_46 =>
                          have assump_963 : p5 := by
                            exact assump_37
                          let assump_57 := assump_41 assump_963
                          apply False.elim assump_57
                    case inr assump_38 =>
                      cases assump_32
                      case intro assump_63 assump_64 =>
                        cases assump_64
                        case inl assump_67 =>
                          have assump_964 : p5 := by
                            exact assump_34
                          let assump_72 := assump_63 assump_964
                          apply False.elim assump_72
                        case inr assump_68 =>
                          have assump_965 : p5 := by
                            exact assump_34
                          let assump_79 := assump_63 assump_965
                          apply False.elim assump_79
                  case inr assump_29 =>
                    apply Or.inl
                    intro assump_85
                    intro assump_86
                    intro assump_87
                    cases assump_86
                    case inl assump_90 =>
                      cases assump_85
                      case intro assump_94 assump_95 =>
                        cases assump_95
                        case inl assump_98 =>
                          have assump_966 : p5 := by
                            exact assump_90
                          let assump_103 := assump_94 assump_966
                          apply False.elim assump_103
                        case inr assump_99 =>
                          have assump_967 : p5 := by
                            exact assump_90
                          let assump_110 := assump_94 assump_967
                          apply False.elim assump_110
                    case inr assump_91 =>
                      cases assump_85
                      case intro assump_116 assump_117 =>
                        cases assump_117
                        case inl assump_120 =>
                          have assump_968 : p5 := by
                            exact assump_87
                          let assump_125 := assump_116 assump_968
                          apply False.elim assump_125
                        case inr assump_121 =>
                          have assump_969 : p5 := by
                            exact assump_87
                          let assump_132 := assump_116 assump_969
                          apply False.elim assump_132
            case inr assump_17 =>
              cases assump_3
              case intro assump_138 assump_139 =>
                cases assump_139
                case inl assump_142 =>
                  apply Or.inl
                  intro assump_146
                  intro assump_147
                  intro assump_148
                  cases assump_147
                  case inl assump_151 =>
                    cases assump_146
                    case intro assump_155 assump_156 =>
                      cases assump_156
                      case inl assump_159 =>
                        have assump_970 : p5 := by
                          exact assump_151
                        let assump_164 := assump_155 assump_970
                        apply False.elim assump_164
                      case inr assump_160 =>
                        have assump_971 : p5 := by
                          exact assump_151
                        let assump_171 := assump_155 assump_971
                        apply False.elim assump_171
                  case inr assump_152 =>
                    cases assump_146
                    case intro assump_177 assump_178 =>
                      cases assump_178
                      case inl assump_181 =>
                        have assump_972 : p5 := by
                          exact assump_148
                        let assump_186 := assump_177 assump_972
                        apply False.elim assump_186
                      case inr assump_182 =>
                        have assump_973 : p5 := by
                          exact assump_148
                        let assump_193 := assump_177 assump_973
                        apply False.elim assump_193
                case inr assump_143 =>
                  apply Or.inl
                  intro assump_199
                  intro assump_200
                  intro assump_201
                  cases assump_200
                  case inl assump_204 =>
                    cases assump_199
                    case intro assump_208 assump_209 =>
                      cases assump_209
                      case inl assump_212 =>
                        have assump_974 : p5 := by
                          exact assump_204
                        let assump_217 := assump_208 assump_974
                        apply False.elim assump_217
                      case inr assump_213 =>
                        have assump_975 : p5 := by
                          exact assump_204
                        let assump_224 := assump_208 assump_975
                        apply False.elim assump_224
                  case inr assump_205 =>
                    cases assump_199
                    case intro assump_230 assump_231 =>
                      cases assump_231
                      case inl assump_234 =>
                        have assump_976 : p5 := by
                          exact assump_201
                        let assump_239 := assump_230 assump_976
                        apply False.elim assump_239
                      case inr assump_235 =>
                        have assump_977 : p5 := by
                          exact assump_201
                        let assump_246 := assump_230 assump_977
                        apply False.elim assump_246
          case inr assump_13 =>
            cases assump_5
            case inl assump_252 =>
              cases assump_252
              case inl assump_254 =>
                apply False.elim assump_254
              case inr assump_255 =>
                cases assump_3
                case intro assump_260 assump_261 =>
                  cases assump_261
                  case inl assump_264 =>
                    apply Or.inl
                    intro assump_268
                    intro assump_269
                    intro assump_270
                    cases assump_269
                    case inl assump_273 =>
                      cases assump_268
                      case intro assump_277 assump_278 =>
                        cases assump_278
                        case inl assump_281 =>
                          have assump_978 : p5 := by
                            exact assump_273
                          let assump_286 := assump_277 assump_978
                          apply False.elim assump_286
                        case inr assump_282 =>
                          have assump_979 : p5 := by
                            exact assump_273
                          let assump_293 := assump_277 assump_979
                          apply False.elim assump_293
                    case inr assump_274 =>
                      cases assump_268
                      case intro assump_299 assump_300 =>
                        cases assump_300
                        case inl assump_303 =>
                          have assump_980 : p5 := by
                            exact assump_270
                          let assump_308 := assump_299 assump_980
                          apply False.elim assump_308
                        case inr assump_304 =>
                          have assump_981 : p5 := by
                            exact assump_270
                          let assump_315 := assump_299 assump_981
                          apply False.elim assump_315
                  case inr assump_265 =>
                    apply Or.inl
                    intro assump_321
                    intro assump_322
                    intro assump_323
                    cases assump_322
                    case inl assump_326 =>
                      cases assump_321
                      case intro assump_330 assump_331 =>
                        cases assump_331
                        case inl assump_334 =>
                          have assump_982 : p5 := by
                            exact assump_326
                          let assump_339 := assump_330 assump_982
                          apply False.elim assump_339
                        case inr assump_335 =>
                          have assump_983 : p5 := by
                            exact assump_326
                          let assump_346 := assump_330 assump_983
                          apply False.elim assump_346
                    case inr assump_327 =>
                      cases assump_321
                      case intro assump_352 assump_353 =>
                        cases assump_353
                        case inl assump_356 =>
                          have assump_984 : p5 := by
                            exact assump_323
                          let assump_361 := assump_352 assump_984
                          apply False.elim assump_361
                        case inr assump_357 =>
                          have assump_985 : p5 := by
                            exact assump_323
                          let assump_368 := assump_352 assump_985
                          apply False.elim assump_368
            case inr assump_253 =>
              cases assump_3
              case intro assump_374 assump_375 =>
                cases assump_375
                case inl assump_378 =>
                  apply Or.inl
                  intro assump_382
                  intro assump_383
                  intro assump_384
                  cases assump_383
                  case inl assump_387 =>
                    cases assump_382
                    case intro assump_391 assump_392 =>
                      cases assump_392
                      case inl assump_395 =>
                        have assump_986 : p5 := by
                          exact assump_387
                        let assump_400 := assump_391 assump_986
                        apply False.elim assump_400
                      case inr assump_396 =>
                        have assump_987 : p5 := by
                          exact assump_387
                        let assump_407 := assump_391 assump_987
                        apply False.elim assump_407
                  case inr assump_388 =>
                    cases assump_382
                    case intro assump_413 assump_414 =>
                      cases assump_414
                      case inl assump_417 =>
                        have assump_988 : p5 := by
                          exact assump_384
                        let assump_422 := assump_413 assump_988
                        apply False.elim assump_422
                      case inr assump_418 =>
                        have assump_989 : p5 := by
                          exact assump_384
                        let assump_429 := assump_413 assump_989
                        apply False.elim assump_429
                case inr assump_379 =>
                  apply Or.inl
                  intro assump_435
                  intro assump_436
                  intro assump_437
                  cases assump_436
                  case inl assump_440 =>
                    cases assump_435
                    case intro assump_444 assump_445 =>
                      cases assump_445
                      case inl assump_448 =>
                        have assump_990 : p5 := by
                          exact assump_440
                        let assump_453 := assump_444 assump_990
                        apply False.elim assump_453
                      case inr assump_449 =>
                        have assump_991 : p5 := by
                          exact assump_440
                        let assump_460 := assump_444 assump_991
                        apply False.elim assump_460
                  case inr assump_441 =>
                    cases assump_435
                    case intro assump_466 assump_467 =>
                      cases assump_467
                      case inl assump_470 =>
                        have assump_992 : p5 := by
                          exact assump_437
                        let assump_475 := assump_466 assump_992
                        apply False.elim assump_475
                      case inr assump_471 =>
                        have assump_993 : p5 := by
                          exact assump_437
                        let assump_482 := assump_466 assump_993
                        apply False.elim assump_482
        case inr assump_9 =>
          cases assump_7
          case inl assump_488 =>
            cases assump_5
            case inl assump_492 =>
              cases assump_492
              case inl assump_494 =>
                apply False.elim assump_494
              case inr assump_495 =>
                cases assump_3
                case intro assump_500 assump_501 =>
                  cases assump_501
                  case inl assump_504 =>
                    apply Or.inl
                    intro assump_508
                    intro assump_509
                    intro assump_510
                    cases assump_509
                    case inl assump_513 =>
                      cases assump_508
                      case intro assump_517 assump_518 =>
                        cases assump_518
                        case inl assump_521 =>
                          have assump_994 : p5 := by
                            exact assump_513
                          let assump_526 := assump_517 assump_994
                          apply False.elim assump_526
                        case inr assump_522 =>
                          have assump_995 : p5 := by
                            exact assump_513
                          let assump_533 := assump_517 assump_995
                          apply False.elim assump_533
                    case inr assump_514 =>
                      cases assump_508
                      case intro assump_539 assump_540 =>
                        cases assump_540
                        case inl assump_543 =>
                          have assump_996 : p5 := by
                            exact assump_510
                          let assump_548 := assump_539 assump_996
                          apply False.elim assump_548
                        case inr assump_544 =>
                          have assump_997 : p5 := by
                            exact assump_510
                          let assump_555 := assump_539 assump_997
                          apply False.elim assump_555
                  case inr assump_505 =>
                    apply Or.inl
                    intro assump_561
                    intro assump_562
                    intro assump_563
                    cases assump_562
                    case inl assump_566 =>
                      cases assump_561
                      case intro assump_570 assump_571 =>
                        cases assump_571
                        case inl assump_574 =>
                          have assump_998 : p5 := by
                            exact assump_566
                          let assump_579 := assump_570 assump_998
                          apply False.elim assump_579
                        case inr assump_575 =>
                          have assump_999 : p5 := by
                            exact assump_566
                          let assump_586 := assump_570 assump_999
                          apply False.elim assump_586
                    case inr assump_567 =>
                      cases assump_561
                      case intro assump_592 assump_593 =>
                        cases assump_593
                        case inl assump_596 =>
                          have assump_1000 : p5 := by
                            exact assump_563
                          let assump_601 := assump_592 assump_1000
                          apply False.elim assump_601
                        case inr assump_597 =>
                          have assump_1001 : p5 := by
                            exact assump_563
                          let assump_608 := assump_592 assump_1001
                          apply False.elim assump_608
            case inr assump_493 =>
              cases assump_3
              case intro assump_614 assump_615 =>
                cases assump_615
                case inl assump_618 =>
                  apply Or.inl
                  intro assump_622
                  intro assump_623
                  intro assump_624
                  cases assump_623
                  case inl assump_627 =>
                    cases assump_622
                    case intro assump_631 assump_632 =>
                      cases assump_632
                      case inl assump_635 =>
                        have assump_1002 : p5 := by
                          exact assump_627
                        let assump_640 := assump_631 assump_1002
                        apply False.elim assump_640
                      case inr assump_636 =>
                        have assump_1003 : p5 := by
                          exact assump_627
                        let assump_647 := assump_631 assump_1003
                        apply False.elim assump_647
                  case inr assump_628 =>
                    cases assump_622
                    case intro assump_653 assump_654 =>
                      cases assump_654
                      case inl assump_657 =>
                        have assump_1004 : p5 := by
                          exact assump_624
                        let assump_662 := assump_653 assump_1004
                        apply False.elim assump_662
                      case inr assump_658 =>
                        have assump_1005 : p5 := by
                          exact assump_624
                        let assump_669 := assump_653 assump_1005
                        apply False.elim assump_669
                case inr assump_619 =>
                  apply Or.inl
                  intro assump_675
                  intro assump_676
                  intro assump_677
                  cases assump_676
                  case inl assump_680 =>
                    cases assump_675
                    case intro assump_684 assump_685 =>
                      cases assump_685
                      case inl assump_688 =>
                        have assump_1006 : p5 := by
                          exact assump_680
                        let assump_693 := assump_684 assump_1006
                        apply False.elim assump_693
                      case inr assump_689 =>
                        have assump_1007 : p5 := by
                          exact assump_680
                        let assump_700 := assump_684 assump_1007
                        apply False.elim assump_700
                  case inr assump_681 =>
                    cases assump_675
                    case intro assump_706 assump_707 =>
                      cases assump_707
                      case inl assump_710 =>
                        have assump_1008 : p5 := by
                          exact assump_677
                        let assump_715 := assump_706 assump_1008
                        apply False.elim assump_715
                      case inr assump_711 =>
                        have assump_1009 : p5 := by
                          exact assump_677
                        let assump_722 := assump_706 assump_1009
                        apply False.elim assump_722
          case inr assump_489 =>
            cases assump_5
            case inl assump_728 =>
              cases assump_728
              case inl assump_730 =>
                apply False.elim assump_730
              case inr assump_731 =>
                cases assump_3
                case intro assump_736 assump_737 =>
                  cases assump_737
                  case inl assump_740 =>
                    apply Or.inl
                    intro assump_744
                    intro assump_745
                    intro assump_746
                    cases assump_745
                    case inl assump_749 =>
                      cases assump_744
                      case intro assump_753 assump_754 =>
                        cases assump_754
                        case inl assump_757 =>
                          have assump_1010 : p5 := by
                            exact assump_749
                          let assump_762 := assump_753 assump_1010
                          apply False.elim assump_762
                        case inr assump_758 =>
                          have assump_1011 : p5 := by
                            exact assump_749
                          let assump_769 := assump_753 assump_1011
                          apply False.elim assump_769
                    case inr assump_750 =>
                      cases assump_744
                      case intro assump_775 assump_776 =>
                        cases assump_776
                        case inl assump_779 =>
                          have assump_1012 : p5 := by
                            exact assump_746
                          let assump_784 := assump_775 assump_1012
                          apply False.elim assump_784
                        case inr assump_780 =>
                          have assump_1013 : p5 := by
                            exact assump_746
                          let assump_791 := assump_775 assump_1013
                          apply False.elim assump_791
                  case inr assump_741 =>
                    apply Or.inl
                    intro assump_797
                    intro assump_798
                    intro assump_799
                    cases assump_798
                    case inl assump_802 =>
                      cases assump_797
                      case intro assump_806 assump_807 =>
                        cases assump_807
                        case inl assump_810 =>
                          have assump_1014 : p5 := by
                            exact assump_802
                          let assump_815 := assump_806 assump_1014
                          apply False.elim assump_815
                        case inr assump_811 =>
                          have assump_1015 : p5 := by
                            exact assump_802
                          let assump_822 := assump_806 assump_1015
                          apply False.elim assump_822
                    case inr assump_803 =>
                      cases assump_797
                      case intro assump_828 assump_829 =>
                        cases assump_829
                        case inl assump_832 =>
                          have assump_1016 : p5 := by
                            exact assump_799
                          let assump_837 := assump_828 assump_1016
                          apply False.elim assump_837
                        case inr assump_833 =>
                          have assump_1017 : p5 := by
                            exact assump_799
                          let assump_844 := assump_828 assump_1017
                          apply False.elim assump_844
            case inr assump_729 =>
              cases assump_3
              case intro assump_850 assump_851 =>
                cases assump_851
                case inl assump_854 =>
                  apply Or.inl
                  intro assump_858
                  intro assump_859
                  intro assump_860
                  cases assump_859
                  case inl assump_863 =>
                    cases assump_858
                    case intro assump_867 assump_868 =>
                      cases assump_868
                      case inl assump_871 =>
                        have assump_1018 : p5 := by
                          exact assump_863
                        let assump_876 := assump_867 assump_1018
                        apply False.elim assump_876
                      case inr assump_872 =>
                        have assump_1019 : p5 := by
                          exact assump_863
                        let assump_883 := assump_867 assump_1019
                        apply False.elim assump_883
                  case inr assump_864 =>
                    cases assump_858
                    case intro assump_889 assump_890 =>
                      cases assump_890
                      case inl assump_893 =>
                        have assump_1020 : p5 := by
                          exact assump_860
                        let assump_898 := assump_889 assump_1020
                        apply False.elim assump_898
                      case inr assump_894 =>
                        have assump_1021 : p5 := by
                          exact assump_860
                        let assump_905 := assump_889 assump_1021
                        apply False.elim assump_905
                case inr assump_855 =>
                  apply Or.inl
                  intro assump_911
                  intro assump_912
                  intro assump_913
                  cases assump_912
                  case inl assump_916 =>
                    cases assump_911
                    case intro assump_920 assump_921 =>
                      cases assump_921
                      case inl assump_924 =>
                        have assump_1022 : p5 := by
                          exact assump_916
                        let assump_929 := assump_920 assump_1022
                        apply False.elim assump_929
                      case inr assump_925 =>
                        have assump_1023 : p5 := by
                          exact assump_916
                        let assump_936 := assump_920 assump_1023
                        apply False.elim assump_936
                  case inr assump_917 =>
                    cases assump_911
                    case intro assump_942 assump_943 =>
                      cases assump_943
                      case inl assump_946 =>
                        have assump_1024 : p5 := by
                          exact assump_913
                        let assump_951 := assump_942 assump_1024
                        apply False.elim assump_951
                      case inr assump_947 =>
                        have assump_1025 : p5 := by
                          exact assump_913
                        let assump_958 := assump_942 assump_1025
                        apply False.elim assump_958


variable (p2 p0 p1 p3 p6 p4 p5 p7 : Prop)
theorem file75_102751 : (((((p4 ∧ p1) ∧ (p3 ∨ p3)) ∧ ((p6 ∨ p3) → False)) → (((p7 ∨ p3) → (p5 ∨ p4)) ∧ ((True → p1) ∧ (p3 → p3)))) ∨ ((((p0 → p4) ∨ (False → False)) → ((p6 ∨ p7) ∧ (p0 → p7))) ∧ (((p2 → False) → (p5 → p7)) → False))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      cases assump_7
      case intro assump_9 assump_10 =>
        cases assump_9
        case intro assump_11 assump_12 =>
          cases assump_10
          case inl assump_17 =>
            apply Or.inr
            exact assump_11
          case inr assump_18 =>
            apply Or.inr
            exact assump_11
  case inr assump_4 =>
    cases assump_1
    case intro assump_29 assump_30 =>
      cases assump_29
      case intro assump_31 assump_32 =>
        cases assump_31
        case intro assump_33 assump_34 =>
          cases assump_32
          case inl assump_39 =>
            apply Or.inr
            exact assump_33
          case inr assump_40 =>
            apply Or.inr
            exact assump_33
  apply And.intro
  intro assump_49
  cases assump_1
  case intro assump_52 assump_53 =>
    cases assump_52
    case intro assump_54 assump_55 =>
      cases assump_54
      case intro assump_56 assump_57 =>
        cases assump_55
        case inl assump_62 =>
          exact assump_57
        case inr assump_63 =>
          exact assump_57
  intro assump_72
  cases assump_1
  case intro assump_75 assump_76 =>
    cases assump_75
    case intro assump_77 assump_78 =>
      cases assump_77
      case intro assump_79 assump_80 =>
        cases assump_78
        case inl assump_85 =>
          exact assump_85
        case inr assump_86 =>
          exact assump_86


variable (p4 p3 p6 p2 p1 p5 p0 p7 : Prop)
theorem file75_104591 : (((((p2 → p5) → (True ∨ p2)) ∨ ((True ∨ p1) ∧ (p7 → p6))) ∨ (((p0 → False) ∨ (p6 ∨ p4)) ∨ ((p1 → p1) → False))) ∨ ((((p1 ∧ p5) → (p4 ∧ p7)) ∧ ((p3 ∨ True) → False)) → (((True ∧ False) → (p3 ∨ p0)) → ((p3 ∨ True) ∧ (False ∧ p4))))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  intro assump_1
  apply Or.inl
  apply True.intro


variable (p5 p3 p2 p7 p0 : Prop)
theorem file75_104981 : ((((((p3 ∧ False) ∧ (p7 ∨ p0)) ∧ ((p3 → p7) → (p2 ∨ p2))) → (((p5 → False) ∨ (p7 → p0)) → False)) → False) → False) := by
  intro assump_1
  have assump_36 : ((((p3 ∧ False) ∧ (p7 ∨ p0)) ∧ ((p3 → p7) → (p2 ∨ p2))) → (((p5 → False) ∨ (p7 → p0)) → False)) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      cases assump_5
      case intro assump_11 assump_12 =>
        cases assump_11
        case intro assump_13 assump_14 =>
          cases assump_13
          case intro assump_15 assump_16 =>
            apply False.elim assump_16
    case inr assump_8 =>
      cases assump_5
      case intro assump_23 assump_24 =>
        cases assump_23
        case intro assump_25 assump_26 =>
          cases assump_25
          case intro assump_27 assump_28 =>
            apply False.elim assump_28
  let assump_4 := assump_1 assump_36
  apply False.elim assump_4


variable (p4 p0 p6 p3 p2 : Prop)
theorem file75_105942 : ((((((True ∨ p4) ∨ (p2 ∨ p3)) → ((p4 → p0) → (False → False))) → False) ∨ ((((False → False) ∧ (p3 → p3)) ∨ ((p0 → False) → (p4 ∧ p6))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case inl assump_2 =>
    have assump_27 : (((True ∨ p4) ∨ (p2 ∨ p3)) → ((p4 → p0) → (False → False))) := by
      intro assump_7
      intro assump_8
      intro assump_9
      apply False.elim assump_9
    let assump_6 := assump_2 assump_27
    apply False.elim assump_6
  case inr assump_3 =>
    have assump_28 : (((False → False) ∧ (p3 → p3)) ∨ ((p0 → False) → (p4 ∧ p6))) := by
      apply Or.inl
      apply And.intro
      intro assump_18
      apply False.elim assump_18
      intro assump_21
      exact assump_21
    let assump_17 := assump_3 assump_28
    apply False.elim assump_17


variable (p5 p4 p1 p6 p0 p2 p7 : Prop)
theorem file75_106796 : (((((False ∨ p7) ∧ (p2 ∧ p6)) → ((p7 → False) → False)) ∨ (((p7 ∨ p7) ∧ (p5 → p4)) → ((p6 → False) ∧ (p5 ∧ p2)))) → ((((p2 → True) → False) ∨ ((p1 ∧ p4) ∧ (p0 ∧ False))) → False)) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case inl assump_7 =>
      have assump_39 : (p2 → True) := by
        intro assump_13
        apply True.intro
      let assump_12 := assump_3 assump_39
      apply False.elim assump_12
    case inr assump_8 =>
      have assump_40 : (p2 → True) := by
        intro assump_21
        apply True.intro
      let assump_20 := assump_3 assump_40
      apply False.elim assump_20
  case inr assump_4 =>
    cases assump_4
    case intro assump_25 assump_26 =>
      cases assump_25
      case intro assump_27 assump_28 =>
        cases assump_26
        case intro assump_33 assump_34 =>
          apply False.elim assump_34


variable (p1 p4 p5 p6 p7 p2 p0 : Prop)
theorem file75_107763 : ((((((p1 → p5) → False) → ((p1 → p0) ∨ (p4 → False))) → (((p5 → False) ∨ (p6 ∧ p4)) → ((False → False) ∨ (p2 → p7)))) → False) → False) := by
  intro assump_1
  have assump_30 : ((((p1 → p5) → False) → ((p1 → p0) ∨ (p4 → False))) → (((p5 → False) ∨ (p6 ∧ p4)) → ((False → False) ∨ (p2 → p7)))) := by
    intro assump_5
    intro assump_6
    cases assump_6
    case inl assump_7 =>
      apply Or.inl
      intro assump_13
      apply False.elim assump_13
    case inr assump_8 =>
      cases assump_8
      case intro assump_16 assump_17 =>
        apply Or.inl
        intro assump_24
        apply False.elim assump_24
  let assump_4 := assump_1 assump_30
  apply False.elim assump_4


variable (p2 p7 p0 p4 p5 p3 p1 : Prop)
theorem file75_108513 : ((((((p1 ∨ p4) → False) ∧ ((p2 ∧ False) ∧ (p1 → False))) → (((False ∨ False) ∨ (p4 ∧ p0)) ∨ ((p0 ∧ p5) → False))) ∧ ((((p3 ∧ p3) → (p7 → p5)) ∧ ((p0 → p5) → (p7 ∨ p3))) ∧ (((p1 ∧ p2) ∨ (False → False)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        have assump_23 : ((p1 ∧ p2) ∨ (False → False)) := by
          apply Or.inr
          intro assump_17
          apply False.elim assump_17
        let assump_16 := assump_7 assump_23
        apply False.elim assump_16


variable (p6 p1 p0 : Prop)
theorem file75_109200 : ((((((False ∧ p1) → False) ∧ ((p6 → False) ∧ (p0 ∧ False))) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((False ∧ p1) → False) ∧ ((p6 → False) ∧ (p0 ∧ False))) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_7
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          apply False.elim assump_15
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p5 p1 p3 p0 p2 p7 p4 p6 : Prop)
theorem file75_109771 : ((((((p6 ∨ p3) → False) ∨ ((p7 ∨ True) ∨ (p0 → p0))) → (((False ∧ p5) → (p4 → False)) ∨ ((p4 → p4) ∧ (p5 → False)))) ∧ ((((False ∨ p2) ∧ (p7 → False)) ∨ ((p1 → p1) → (p6 → False))) ∧ (((p4 → False) → (p0 → False)) ∧ ((p6 → False) ∧ (p5 ∧ p6))))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case inl assump_8 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case inl assump_12 =>
            apply False.elim assump_12
          case inr assump_13 =>
            cases assump_7
            case intro assump_20 assump_21 =>
              cases assump_21
              case intro assump_24 assump_25 =>
                cases assump_25
                case intro assump_28 assump_29 =>
                  have assump_62 : p6 := by
                    exact assump_29
                  let assump_36 := assump_24 assump_62
                  apply False.elim assump_36
      case inr assump_9 =>
        cases assump_7
        case intro assump_42 assump_43 =>
          cases assump_43
          case intro assump_46 assump_47 =>
            cases assump_47
            case intro assump_50 assump_51 =>
              have assump_63 : p6 := by
                exact assump_51
              let assump_58 := assump_46 assump_63
              apply False.elim assump_58


variable (p7 p2 p4 p3 p6 p1 p0 p5 : Prop)
theorem file75_111276 : (((((p3 ∧ p4) ∧ (p4 ∧ p3)) → ((p1 → p0) ∧ (p5 → False))) ∨ (((p6 → p1) ∧ (p0 ∧ p7)) → False)) → ((((p2 → True) ∨ (p7 ∨ True)) ∧ ((p5 ∨ p4) ∧ (p3 ∧ p6))) → (((p5 → False) → False) → ((False → False) ∨ (p5 → p1))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_2
  case intro assump_6 assump_7 =>
    cases assump_6
    case inl assump_8 =>
      cases assump_7
      case intro assump_12 assump_13 =>
        cases assump_12
        case inl assump_14 =>
          cases assump_13
          case intro assump_18 assump_19 =>
            cases assump_1
            case inl assump_24 =>
              apply Or.inl
              intro assump_28
              apply False.elim assump_28
            case inr assump_25 =>
              apply Or.inl
              intro assump_33
              apply False.elim assump_33
        case inr assump_15 =>
          cases assump_13
          case intro assump_38 assump_39 =>
            cases assump_1
            case inl assump_44 =>
              apply Or.inl
              intro assump_48
              apply False.elim assump_48
            case inr assump_45 =>
              apply Or.inl
              intro assump_53
              apply False.elim assump_53
    case inr assump_9 =>
      cases assump_9
      case inl assump_56 =>
        cases assump_7
        case intro assump_60 assump_61 =>
          cases assump_60
          case inl assump_62 =>
            cases assump_61
            case intro assump_66 assump_67 =>
              cases assump_1
              case inl assump_72 =>
                apply Or.inl
                intro assump_76
                apply False.elim assump_76
              case inr assump_73 =>
                apply Or.inl
                intro assump_81
                apply False.elim assump_81
          case inr assump_63 =>
            cases assump_61
            case intro assump_86 assump_87 =>
              cases assump_1
              case inl assump_92 =>
                apply Or.inl
                intro assump_96
                apply False.elim assump_96
              case inr assump_93 =>
                apply Or.inl
                intro assump_101
                apply False.elim assump_101
      case inr assump_57 =>
        cases assump_7
        case intro assump_106 assump_107 =>
          cases assump_106
          case inl assump_108 =>
            cases assump_107
            case intro assump_112 assump_113 =>
              cases assump_1
              case inl assump_118 =>
                apply Or.inl
                intro assump_122
                apply False.elim assump_122
              case inr assump_119 =>
                apply Or.inl
                intro assump_127
                apply False.elim assump_127
          case inr assump_109 =>
            cases assump_107
            case intro assump_132 assump_133 =>
              cases assump_1
              case inl assump_138 =>
                apply Or.inl
                intro assump_142
                apply False.elim assump_142
              case inr assump_139 =>
                apply Or.inl
                intro assump_147
                apply False.elim assump_147


variable (p2 p0 p7 p1 p4 p3 p6 p5 : Prop)
theorem file75_114544 : (((((p6 ∧ p7) ∨ (p5 ∨ p5)) ∧ ((True → False) ∧ (p1 ∧ True))) → (((p2 → False) → False) → ((p6 ∧ p5) → (p2 ∨ False)))) ∨ ((((p2 ∧ p0) → (p1 → p4)) ∧ ((p2 → False) ∨ (p2 → False))) ∨ (((p2 ∨ p1) → (p5 ∨ p5)) ∧ ((p6 → p3) → (False → False))))) := by
  apply Or.inl
  intro assump_113
  intro assump_114
  intro assump_115
  cases assump_115
  case intro assump_116 assump_117 =>
    cases assump_113
    case intro assump_124 assump_125 =>
      cases assump_124
      case inl assump_126 =>
        cases assump_126
        case intro assump_128 assump_129 =>
          cases assump_125
          case intro assump_134 assump_135 =>
            cases assump_135
            case intro assump_138 assump_139 =>
              have assump_185 : True := by
                apply True.intro
              let assump_145 := assump_134 assump_185
              apply False.elim assump_145
      case inr assump_127 =>
        cases assump_127
        case inl assump_149 =>
          cases assump_125
          case intro assump_153 assump_154 =>
            cases assump_154
            case intro assump_157 assump_158 =>
              have assump_186 : True := by
                apply True.intro
              let assump_164 := assump_153 assump_186
              apply False.elim assump_164
        case inr assump_150 =>
          cases assump_125
          case intro assump_170 assump_171 =>
            cases assump_171
            case intro assump_174 assump_175 =>
              have assump_187 : True := by
                apply True.intro
              let assump_181 := assump_170 assump_187
              apply False.elim assump_181


variable (p0 p1 p7 p2 p5 p6 p4 p3 : Prop)
theorem file75_116250 : (((((True → False) ∧ (p7 ∨ True)) → ((p5 ∨ p1) ∨ (p7 → False))) → (((p6 → p0) ∨ (p5 ∨ p0)) ∧ ((p7 ∧ p7) → (p7 ∨ p7)))) → ((((p1 ∧ p2) → (p7 → p2)) ∨ ((False → True) → (p2 → p4))) ∧ (((p0 ∨ False) ∧ (p1 ∧ False)) → ((p5 ∧ True) ∨ (False → p3))))) := by
  intro assump_1
  apply And.intro
  apply Or.inl
  intro assump_4
  intro assump_5
  cases assump_4
  case intro assump_8 assump_9 =>
    exact assump_9
  intro assump_14
  cases assump_14
  case intro assump_15 assump_16 =>
    cases assump_15
    case inl assump_17 =>
      cases assump_16
      case intro assump_21 assump_22 =>
        apply False.elim assump_22
    case inr assump_18 =>
      apply False.elim assump_18


variable (p6 p3 p0 p2 p1 p7 p5 : Prop)
theorem file75_116993 : ((((((p0 ∧ p5) → (p2 → False)) → ((p6 ∧ False) → (False → p3))) ∨ (((p6 ∧ p1) ∨ (p7 ∧ p7)) ∨ ((p1 ∧ p7) → False))) → False) → False) := by
  intro assump_1
  have assump_13 : ((((p0 ∧ p5) → (p2 → False)) → ((p6 ∧ False) → (False → p3))) ∨ (((p6 ∧ p1) ∨ (p7 ∧ p7)) ∨ ((p1 ∧ p7) → False))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    intro assump_7
    apply False.elim assump_7
  let assump_4 := assump_1 assump_13
  apply False.elim assump_4


variable (p7 p1 p0 p3 p6 : Prop)
theorem file75_117513 : ((((((p6 → p0) ∨ (p7 → False)) → False) ∨ (((p1 → False) → False) ∧ ((p3 ∨ True) → (p7 → False)))) ∧ ((((p0 → False) → (True ∨ p6)) ∨ ((p6 ∧ True) ∨ (p6 ∧ False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_32 : (((p0 → False) → (True ∨ p6)) ∨ ((p6 ∧ True) ∨ (p6 ∧ False))) := by
        apply Or.inl
        intro assump_11
        apply Or.inl
        apply True.intro
      let assump_10 := assump_3 assump_32
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case intro assump_17 assump_18 =>
        have assump_33 : (((p0 → False) → (True ∨ p6)) ∨ ((p6 ∧ True) ∨ (p6 ∧ False))) := by
          apply Or.inl
          intro assump_26
          apply Or.inl
          apply True.intro
        let assump_25 := assump_3 assump_33
        apply False.elim assump_25


variable (p4 p3 p1 p0 p2 p6 p5 : Prop)
theorem file75_118491 : (((((True ∧ p1) ∨ (p5 ∨ True)) → False) → (((p4 ∧ p3) ∨ (False ∧ p0)) → ((p6 ∨ p5) → (p6 ∧ p2)))) ∨ ((((p3 ∧ p3) → (False → False)) ∧ ((p5 → False) ∧ (False ∧ p2))) ∧ (((p3 → p4) ∨ (p4 → p3)) ∨ ((p4 ∧ p5) ∨ (p4 → p1))))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_2
    case inl assump_8 =>
      cases assump_8
      case intro assump_10 assump_11 =>
        exact assump_4
    case inr assump_9 =>
      cases assump_9
      case intro assump_18 assump_19 =>
        apply False.elim assump_18
  case inr assump_5 =>
    cases assump_2
    case inl assump_24 =>
      cases assump_24
      case intro assump_26 assump_27 =>
        have assump_84 : ((True ∧ p1) ∨ (p5 ∨ True)) := by
          apply Or.inr
          apply Or.inl
          exact assump_5
        let assump_34 := assump_1 assump_84
        apply False.elim assump_34
    case inr assump_25 =>
      cases assump_25
      case intro assump_38 assump_39 =>
        apply False.elim assump_38
  cases assump_3
  case inl assump_42 =>
    cases assump_2
    case inl assump_46 =>
      cases assump_46
      case intro assump_48 assump_49 =>
        have assump_85 : ((True ∧ p1) ∨ (p5 ∨ True)) := by
          apply Or.inr
          apply Or.inr
          apply True.intro
        let assump_56 := assump_1 assump_85
        apply False.elim assump_56
    case inr assump_47 =>
      cases assump_47
      case intro assump_60 assump_61 =>
        apply False.elim assump_60
  case inr assump_43 =>
    cases assump_2
    case inl assump_66 =>
      cases assump_66
      case intro assump_68 assump_69 =>
        have assump_86 : ((True ∧ p1) ∨ (p5 ∨ True)) := by
          apply Or.inr
          apply Or.inl
          exact assump_43
        let assump_76 := assump_1 assump_86
        apply False.elim assump_76
    case inr assump_67 =>
      cases assump_67
      case intro assump_80 assump_81 =>
        apply False.elim assump_80


variable (p0 p3 p7 p2 p1 p5 p4 : Prop)
theorem file75_120562 : (((((p7 ∨ p5) ∧ (p3 ∧ False)) → False) ∨ (((True ∨ p7) ∨ (p0 ∧ p0)) → ((p1 → False) → (False ∧ p3)))) ∨ ((((p7 → False) → False) → ((p5 ∧ False) → False)) ∧ (((p3 → p4) → False) ∨ ((p2 ∧ p7) → False)))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      cases assump_3
      case intro assump_8 assump_9 =>
        apply False.elim assump_9
    case inr assump_5 =>
      cases assump_3
      case intro assump_16 assump_17 =>
        apply False.elim assump_17


variable (p5 p1 p0 : Prop)
theorem file75_121178 : (((((False → p5) ∨ (p5 ∧ True)) ∨ ((p0 → False) → (p1 → False))) → False) → False) := by
  intro assump_1
  have assump_11 : (((False → p5) ∨ (p5 ∧ True)) ∨ ((p0 → False) → (p1 → False))) := by
    apply Or.inl
    apply Or.inl
    intro assump_5
    apply False.elim assump_5
  let assump_4 := assump_1 assump_11
  apply False.elim assump_4


variable (p7 p5 p0 p6 : Prop)
theorem file75_121574 : ((((((False ∧ p7) → False) → False) → (((True → False) → False) ∧ ((p6 → False) → (p0 ∨ p5)))) → False) → False) := by
  intro assump_1
  have assump_37 : ((((False ∧ p7) → False) → False) → (((True → False) → False) ∧ ((p6 → False) → (p0 ∨ p5)))) := by
    intro assump_5
    apply And.intro
    intro assump_6
    have assump_38 : ((False ∧ p7) → False) := by
      intro assump_12
      cases assump_12
      case intro assump_13 assump_14 =>
        apply False.elim assump_13
    let assump_11 := assump_5 assump_38
    apply False.elim assump_11
    intro assump_20
    have assump_39 : ((False ∧ p7) → False) := by
      intro assump_26
      cases assump_26
      case intro assump_27 assump_28 =>
        apply False.elim assump_27
    let assump_25 := assump_5 assump_39
    apply False.elim assump_25
  let assump_4 := assump_1 assump_37
  apply False.elim assump_4


variable (p1 : Prop)
theorem file75_122496 : ((((((p1 → p1) → False) ∧ ((False ∧ p1) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_23 : ((((p1 → p1) → False) ∧ ((False ∧ p1) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      have assump_24 : (p1 → p1) := by
        intro assump_14
        exact assump_14
      let assump_13 := assump_6 assump_24
      apply False.elim assump_13
  let assump_4 := assump_1 assump_23
  apply False.elim assump_4


variable (p7 p1 p4 p6 p3 : Prop)
theorem file75_123036 : ((((((p1 → True) → False) → ((p1 → False) → (p1 ∨ True))) ∨ (((p7 → False) → (False ∨ p6)) ∨ ((p6 → p3) ∧ (p4 → False)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p1 → True) → False) → ((p1 → False) → (p1 ∨ True))) ∨ (((p7 → False) → (False ∨ p6)) ∨ ((p6 → p3) ∧ (p4 → False)))) := by
    apply Or.inl
    intro assump_5
    intro assump_6
    apply Or.inr
    apply True.intro
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


variable (p6 p2 p0 p4 p7 p5 p1 : Prop)
theorem file75_123565 : (((((p4 ∨ False) ∨ (p0 → False)) ∧ ((True → False) ∧ (p6 ∧ p6))) → False) → ((((p1 ∧ p2) → (False ∨ p7)) ∧ ((p5 → p5) ∧ (False ∧ p4))) → (((p7 ∨ p2) ∨ (p6 ∨ p5)) → ((p7 ∧ False) ∧ (False ∨ p5))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  apply And.intro
  apply And.intro
  cases assump_3
  case inl assump_4 =>
    cases assump_4
    case inl assump_6 =>
      cases assump_2
      case intro assump_10 assump_11 =>
        cases assump_11
        case intro assump_14 assump_15 =>
          cases assump_15
          case intro assump_18 assump_19 =>
            apply False.elim assump_18
    case inr assump_7 =>
      cases assump_2
      case intro assump_24 assump_25 =>
        cases assump_25
        case intro assump_28 assump_29 =>
          cases assump_29
          case intro assump_32 assump_33 =>
            apply False.elim assump_32
  case inr assump_5 =>
    cases assump_5
    case inl assump_36 =>
      cases assump_2
      case intro assump_40 assump_41 =>
        cases assump_41
        case intro assump_44 assump_45 =>
          cases assump_45
          case intro assump_48 assump_49 =>
            apply False.elim assump_48
    case inr assump_37 =>
      cases assump_2
      case intro assump_54 assump_55 =>
        cases assump_55
        case intro assump_58 assump_59 =>
          cases assump_59
          case intro assump_62 assump_63 =>
            apply False.elim assump_62
  cases assump_3
  case inl assump_66 =>
    cases assump_66
    case inl assump_68 =>
      cases assump_2
      case intro assump_72 assump_73 =>
        cases assump_73
        case intro assump_76 assump_77 =>
          cases assump_77
          case intro assump_80 assump_81 =>
            apply False.elim assump_80
    case inr assump_69 =>
      cases assump_2
      case intro assump_86 assump_87 =>
        cases assump_87
        case intro assump_90 assump_91 =>
          cases assump_91
          case intro assump_94 assump_95 =>
            apply False.elim assump_94
  case inr assump_67 =>
    cases assump_67
    case inl assump_98 =>
      cases assump_2
      case intro assump_102 assump_103 =>
        cases assump_103
        case intro assump_106 assump_107 =>
          cases assump_107
          case intro assump_110 assump_111 =>
            apply False.elim assump_110
    case inr assump_99 =>
      cases assump_2
      case intro assump_116 assump_117 =>
        cases assump_117
        case intro assump_120 assump_121 =>
          cases assump_121
          case intro assump_124 assump_125 =>
            apply False.elim assump_124
  cases assump_3
  case inl assump_128 =>
    cases assump_128
    case inl assump_130 =>
      cases assump_2
      case intro assump_134 assump_135 =>
        cases assump_135
        case intro assump_138 assump_139 =>
          cases assump_139
          case intro assump_142 assump_143 =>
            apply False.elim assump_142
    case inr assump_131 =>
      cases assump_2
      case intro assump_148 assump_149 =>
        cases assump_149
        case intro assump_152 assump_153 =>
          cases assump_153
          case intro assump_156 assump_157 =>
            apply False.elim assump_156
  case inr assump_129 =>
    cases assump_129
    case inl assump_160 =>
      cases assump_2
      case intro assump_164 assump_165 =>
        cases assump_165
        case intro assump_168 assump_169 =>
          cases assump_169
          case intro assump_172 assump_173 =>
            apply False.elim assump_172
    case inr assump_161 =>
      cases assump_2
      case intro assump_178 assump_179 =>
        cases assump_179
        case intro assump_182 assump_183 =>
          cases assump_183
          case intro assump_186 assump_187 =>
            apply False.elim assump_186


variable (p4 p5 p1 p0 p7 : Prop)
theorem file75_127427 : (((((False → p4) ∧ (p7 → p7)) → False) → False) ∧ ((((p7 ∧ p7) → (False → False)) ∨ ((p0 → True) → False)) ∨ (((p1 ∧ p1) ∨ (p7 → False)) ∨ ((p5 → False) → (p0 ∧ p7))))) := by
  apply And.intro
  intro assump_1
  have assump_18 : ((False → p4) ∧ (p7 → p7)) := by
    apply And.intro
    intro assump_5
    apply False.elim assump_5
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_18
  apply False.elim assump_4
  apply Or.inl
  apply Or.inl
  intro assump_14
  intro assump_15
  apply False.elim assump_15


variable (p4 p7 p5 p2 p1 : Prop)
theorem file75_128013 : ((((((p5 ∨ p5) → (p5 ∨ p2)) ∧ ((False ∨ p4) ∨ (p4 ∨ p5))) ∨ (((p5 → False) ∧ (p2 ∧ p7)) ∨ ((p1 → p4) → (p5 → p4)))) → False) → False) := by
  intro assump_1
  have assump_49 : ((((p5 ∨ p5) → (p5 ∨ p2)) ∧ ((False ∨ p4) ∨ (p4 ∨ p5))) ∨ (((p5 → False) ∧ (p2 ∧ p7)) ∨ ((p1 → p4) → (p5 → p4)))) := by
    apply Or.inr
    apply Or.inr
    intro assump_27
    intro assump_28
    have assump_50 : ((((p5 ∨ p5) → (p5 ∨ p2)) ∧ ((False ∨ p4) ∨ (p4 ∨ p5))) ∨ (((p5 → False) ∧ (p2 ∧ p7)) ∨ ((p1 → p4) → (p5 → p4)))) := by
      apply Or.inl
      apply And.intro
      intro assump_36
      cases assump_36
      case inl assump_37 =>
        apply Or.inl
        exact assump_37
      case inr assump_38 =>
        apply Or.inl
        exact assump_38
      apply Or.inr
      apply Or.inr
      exact assump_28
    let assump_35 := assump_1 assump_50
    apply False.elim assump_35
  let assump_4 := assump_1 assump_49
  apply False.elim assump_4


variable (p7 p0 p3 p4 p1 p2 p5 p6 : Prop)
theorem file75_129017 : (((((p6 ∨ p3) ∧ (p6 ∨ p3)) → False) ∨ (((p5 → p7) ∨ (p6 → False)) ∨ ((False → p1) → (p0 ∨ p2)))) → ((((True → False) → False) ∨ ((p4 ∧ p4) → (p4 ∧ p7))) → (((p1 ∨ False) ∨ (p3 → p3)) ∨ ((True ∧ p0) ∨ (False ∧ p2))))) := by
  intro assump_118
  intro assump_119
  cases assump_119
  case inl assump_120 =>
    cases assump_118
    case inl assump_124 =>
      apply Or.inl
      apply Or.inr
      intro assump_128
      exact assump_128
    case inr assump_125 =>
      cases assump_125
      case inl assump_131 =>
        cases assump_131
        case inl assump_133 =>
          apply Or.inl
          apply Or.inr
          intro assump_137
          exact assump_137
        case inr assump_134 =>
          apply Or.inl
          apply Or.inr
          intro assump_142
          exact assump_142
      case inr assump_132 =>
        apply Or.inl
        apply Or.inr
        intro assump_147
        exact assump_147
  case inr assump_121 =>
    cases assump_118
    case inl assump_152 =>
      apply Or.inl
      apply Or.inr
      intro assump_156
      exact assump_156
    case inr assump_153 =>
      cases assump_153
      case inl assump_159 =>
        cases assump_159
        case inl assump_161 =>
          apply Or.inl
          apply Or.inr
          intro assump_165
          exact assump_165
        case inr assump_162 =>
          apply Or.inl
          apply Or.inr
          intro assump_170
          exact assump_170
      case inr assump_160 =>
        apply Or.inl
        apply Or.inr
        intro assump_175
        exact assump_175


variable (p5 p7 p6 p2 : Prop)
theorem file75_130639 : (((((p6 → True) ∨ (p7 → False)) → False) → (((p2 → False) → False) → False)) ∨ ((((True ∧ p5) → False) ∧ ((True ∧ True) ∧ (p5 → p5))) → False)) := by
  apply Or.inl
  intro assump_21
  intro assump_22
  have assump_32 : ((p6 → True) ∨ (p7 → False)) := by
    apply Or.inl
    intro assump_28
    apply True.intro
  let assump_27 := assump_21 assump_32
  apply False.elim assump_27


variable (p0 p7 p3 p5 p4 p2 : Prop)
theorem file75_131080 : (((((p0 ∨ p5) → False) → False) → False) → ((((p5 → False) ∨ (p7 ∧ True)) ∨ ((p4 ∧ p5) ∧ (p0 → False))) → (((True ∨ p2) ∨ (True → False)) ∨ ((True ∨ p4) → (p3 → p7))))) := by
  intro assump_1
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_3
    case inl assump_5 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_6 =>
      cases assump_6
      case intro assump_11 assump_12 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro
  case inr assump_4 =>
    cases assump_4
    case intro assump_19 assump_20 =>
      cases assump_19
      case intro assump_21 assump_22 =>
        apply Or.inl
        apply Or.inl
        apply Or.inl
        apply True.intro


variable (p2 p6 p1 p7 p3 p4 p0 p5 : Prop)
theorem file75_131923 : (((((p5 ∨ False) ∧ (True → False)) → ((False → False) → False)) ∨ (((p3 ∨ p6) ∧ (True ∨ p2)) → ((p3 ∧ p6) → (p0 → True)))) ∨ ((((p6 ∧ p4) ∧ (p7 ∧ p1)) ∧ ((p7 ∨ p4) → False)) ∧ (((p5 → p1) → (p3 ∧ p7)) → False))) := by
  apply Or.inl
  apply Or.inl
  intro assump_1
  intro assump_2
  cases assump_1
  case intro assump_5 assump_6 =>
    cases assump_5
    case inl assump_7 =>
      have assump_19 : True := by
        apply True.intro
      let assump_13 := assump_6 assump_19
      apply False.elim assump_13
    case inr assump_8 =>
      apply False.elim assump_8


variable (p0 p4 p6 p5 p1 p2 p3 : Prop)
theorem file75_132554 : (((((p6 ∧ p5) ∧ (p2 ∨ False)) → False) ∧ (((p2 → False) → False) → ((True ∧ p3) ∨ (p4 ∨ p3)))) → ((((p5 ∧ p2) ∧ (True → False)) → False) → (((p1 → p3) → (p4 → p3)) → ((p2 ∧ p4) ∨ (True ∨ p0))))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  cases assump_1
  case intro assump_8 assump_9 =>
    apply Or.inr
    apply Or.inl
    apply True.intro


variable (p7 p3 p1 p0 p5 p2 p6 p4 : Prop)
theorem file75_132978 : (((((p1 ∨ True) → (False ∨ p3)) ∧ ((p3 → False) ∨ (p3 → True))) → (((True ∨ p2) ∨ (p0 ∧ p6)) ∨ ((p5 → False) → (p0 → False)))) ∨ ((((p7 → p3) → False) → False) ∨ (((p0 ∨ False) ∧ (p6 → p4)) → False))) := by
  apply Or.inl
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case inl assump_6 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro
    case inr assump_7 =>
      apply Or.inl
      apply Or.inl
      apply Or.inl
      apply True.intro


theorem file75_133521 : (((((False → False) → False) → False) → False) → False) := by
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


variable (p2 p6 p3 p5 p4 p7 p0 : Prop)
theorem file75_133973 : ((((((p4 → False) → False) → False) → (((p6 → p5) → False) ∨ ((p2 → p0) ∧ (p4 → False)))) ∧ ((((True ∧ True) ∧ (p2 ∧ False)) ∧ ((p7 → False) → (p0 ∧ p3))) ∧ (((True ∨ p0) ∧ (p5 ∧ p3)) → False))) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_3
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_8
        case intro assump_10 assump_11 =>
          cases assump_10
          case intro assump_12 assump_13 =>
            cases assump_11
            case intro assump_18 assump_19 =>
              apply False.elim assump_19


variable (p1 p5 p6 p7 p4 p0 p3 : Prop)
theorem file75_134678 : ((((((p5 ∧ False) → (p4 ∨ p3)) ∧ ((p0 → False) → False)) → (((p4 → p6) → (p7 ∧ p1)) → ((p0 ∧ p0) ∨ (False → p1)))) → False) → False) := by
  intro assump_1
  have assump_21 : ((((p5 ∧ False) → (p4 ∨ p3)) ∧ ((p0 → False) → False)) → (((p4 → p6) → (p7 ∧ p1)) → ((p0 ∧ p0) ∨ (False → p1)))) := by
    intro assump_5
    intro assump_6
    cases assump_5
    case intro assump_9 assump_10 =>
      apply Or.inr
      intro assump_15
      apply False.elim assump_15
  let assump_4 := assump_1 assump_21
  apply False.elim assump_4


variable (p1 p3 p0 p2 p5 : Prop)
theorem file75_135262 : (((((False ∧ False) → False) → False) → (((p1 ∨ p0) → False) → ((p1 → False) → False))) ∨ ((((p3 ∨ p2) → False) → False) ∧ (((p1 ∨ p3) ∧ (p0 ∨ p2)) ∧ ((True → False) ∧ (True → p5))))) := by
  apply Or.inl
  intro assump_67
  intro assump_68
  intro assump_69
  have assump_85 : ((False ∧ False) → False) := by
    intro assump_77
    cases assump_77
    case intro assump_78 assump_79 =>
      apply False.elim assump_78
  let assump_76 := assump_67 assump_85
  apply False.elim assump_76


variable (p3 p7 p4 p6 : Prop)
theorem file75_135805 : ((((((p7 → p4) ∧ (p7 ∨ p6)) ∧ ((False → p3) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_39 : ((((p7 → p4) ∧ (p7 ∨ p6)) ∧ ((False → p3) → False)) → False) := by
    intro assump_5
    cases assump_5
    case intro assump_6 assump_7 =>
      cases assump_6
      case intro assump_8 assump_9 =>
        cases assump_9
        case inl assump_12 =>
          have assump_40 : (False → p3) := by
            intro assump_19
            apply False.elim assump_19
          let assump_18 := assump_7 assump_40
          apply False.elim assump_18
        case inr assump_13 =>
          have assump_41 : (False → p3) := by
            intro assump_30
            apply False.elim assump_30
          let assump_29 := assump_7 assump_41
          apply False.elim assump_29
  let assump_4 := assump_1 assump_39
  apply False.elim assump_4


variable (p3 p4 p5 p2 p1 p0 p6 : Prop)
theorem file75_136731 : (((((p2 → False) ∧ (True → False)) ∨ ((p5 ∧ True) ∧ (True → False))) → (((p1 → p3) ∧ (p3 → False)) → ((False ∨ True) ∧ (p4 ∨ p2)))) ∨ ((((p2 ∧ p1) ∨ (False ∧ True)) ∧ ((p0 → p4) ∨ (p2 → False))) → (((False → False) ∧ (p5 ∧ p6)) → False))) := by
  apply Or.inl
  intro assump_1
  intro assump_2
  apply And.intro
  cases assump_2
  case intro assump_3 assump_4 =>
    cases assump_1
    case inl assump_9 =>
      cases assump_9
      case intro assump_11 assump_12 =>
        apply Or.inr
        apply True.intro
    case inr assump_10 =>
      cases assump_10
      case intro assump_17 assump_18 =>
        cases assump_17
        case intro assump_19 assump_20 =>
          apply Or.inr
          apply True.intro
  cases assump_2
  case intro assump_27 assump_28 =>
    cases assump_1
    case inl assump_33 =>
      cases assump_33
      case intro assump_35 assump_36 =>
        have assump_59 : True := by
          apply True.intro
        let assump_41 := assump_36 assump_59
        apply False.elim assump_41
    case inr assump_34 =>
      cases assump_34
      case intro assump_45 assump_46 =>
        cases assump_45
        case intro assump_47 assump_48 =>
          have assump_60 : True := by
            apply True.intro
          let assump_55 := assump_46 assump_60
          apply False.elim assump_55


variable (p0 p1 p7 p5 p4 p6 p2 : Prop)
theorem file75_138120 : ((((((p2 → p0) ∨ (False → False)) → ((p7 ∨ p1) ∨ (p6 ∧ p7))) ∨ (((p5 → False) → (p6 → p1)) ∨ ((p1 ∧ p4) → (p5 ∧ p2)))) ∧ ((((p2 ∨ p2) ∧ (p6 ∨ p7)) ∨ ((p2 ∧ p2) ∨ (False → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    cases assump_2
    case inl assump_4 =>
      have assump_41 : (((p2 ∨ p2) ∧ (p6 ∨ p7)) ∨ ((p2 ∧ p2) ∨ (False → False))) := by
        apply Or.inr
        apply Or.inr
        intro assump_11
        apply False.elim assump_11
      let assump_10 := assump_3 assump_41
      apply False.elim assump_10
    case inr assump_5 =>
      cases assump_5
      case inl assump_17 =>
        have assump_42 : (((p2 ∨ p2) ∧ (p6 ∨ p7)) ∨ ((p2 ∧ p2) ∨ (False → False))) := by
          apply Or.inr
          apply Or.inr
          intro assump_24
          apply False.elim assump_24
        let assump_23 := assump_3 assump_42
        apply False.elim assump_23
      case inr assump_18 =>
        have assump_43 : (((p2 ∨ p2) ∧ (p6 ∨ p7)) ∨ ((p2 ∧ p2) ∨ (False → False))) := by
          apply Or.inr
          apply Or.inr
          intro assump_35
          apply False.elim assump_35
        let assump_34 := assump_3 assump_43
        apply False.elim assump_34


variable (p1 p4 p3 p2 : Prop)
theorem file75_139410 : ((((((p2 ∧ p1) → (p3 → p1)) → ((True ∨ p4) → False)) → False) → False) → False) := by
  intro assump_1
  have assump_26 : ((((p2 ∧ p1) → (p3 → p1)) → ((True ∨ p4) → False)) → False) := by
    intro assump_5
    have assump_27 : ((p2 ∧ p1) → (p3 → p1)) := by
      intro assump_9
      intro assump_10
      cases assump_9
      case intro assump_13 assump_14 =>
        exact assump_14
    let assump_8 := assump_5 assump_27
    have assump_28 : (True ∨ p4) := by
      apply Or.inl
      apply True.intro
    let assump_19 := assump_8 assump_28
    apply False.elim assump_19
  let assump_4 := assump_1 assump_26
  apply False.elim assump_4


variable (p3 p7 p2 p1 p6 p5 p4 : Prop)
theorem file75_140115 : ((((((p2 ∧ p3) → False) ∨ ((p7 ∨ p3) → False)) → (((p3 ∨ False) ∧ (p6 ∧ p4)) ∧ ((True ∨ p2) ∨ (p2 ∧ p6)))) ∧ ((((p5 ∨ p5) ∨ (p2 ∨ p1)) → ((p2 → p2) ∨ (p7 → False))) → False)) → False) := by
  intro assump_1
  cases assump_1
  case intro assump_2 assump_3 =>
    have assump_39 : (((p5 ∨ p5) ∨ (p2 ∨ p1)) → ((p2 → p2) ∨ (p7 → False))) := by
      intro assump_9
      cases assump_9
      case inl assump_10 =>
        cases assump_10
        case inl assump_12 =>
          apply Or.inl
          intro assump_16
          exact assump_16
        case inr assump_13 =>
          apply Or.inl
          intro assump_21
          exact assump_21
      case inr assump_11 =>
        cases assump_11
        case inl assump_24 =>
          apply Or.inl
          intro assump_28
          exact assump_28
        case inr assump_25 =>
          apply Or.inl
          intro assump_33
          exact assump_33
    let assump_8 := assump_3 assump_39
    apply False.elim assump_8


variable (p6 p2 p3 p7 p0 p5 p4 p1 : Prop)
theorem file75_141156 : (((((False → p2) → False) ∧ ((False → False) → False)) → (((p5 ∨ p0) → False) ∧ ((p4 → False) ∧ (p2 → False)))) ∨ ((((p1 → False) → (False ∧ p0)) ∧ ((p7 ∧ p2) ∧ (True ∧ p4))) ∨ (((p4 ∨ p2) ∨ (p5 ∨ p0)) ∨ ((p6 → p3) → False)))) := by
  apply Or.inl
  intro assump_1
  apply And.intro
  intro assump_2
  cases assump_2
  case inl assump_3 =>
    cases assump_1
    case intro assump_7 assump_8 =>
      have assump_67 : (False → False) := by
        intro assump_14
        apply False.elim assump_14
      let assump_13 := assump_8 assump_67
      apply False.elim assump_13
  case inr assump_4 =>
    cases assump_1
    case intro assump_22 assump_23 =>
      have assump_68 : (False → False) := by
        intro assump_29
        apply False.elim assump_29
      let assump_28 := assump_23 assump_68
      apply False.elim assump_28
  apply And.intro
  intro assump_35
  cases assump_1
  case intro assump_38 assump_39 =>
    have assump_69 : (False → False) := by
      intro assump_45
      apply False.elim assump_45
    let assump_44 := assump_39 assump_69
    apply False.elim assump_44
  intro assump_51
  cases assump_1
  case intro assump_54 assump_55 =>
    have assump_70 : (False → False) := by
      intro assump_61
      apply False.elim assump_61
    let assump_60 := assump_55 assump_70
    apply False.elim assump_60


variable (p4 p3 p7 p6 p1 p0 p5 : Prop)
theorem file75_142553 : (((((p1 ∧ p3) ∨ (p4 → p7)) → ((False → p3) → False)) ∨ (((p6 ∨ p3) → False) ∧ ((p0 ∨ p3) → (p1 ∧ p1)))) → ((((False ∧ p7) ∧ (p0 ∧ p1)) → False) → (((p4 ∧ True) ∧ (p1 ∧ p4)) → ((p3 ∧ p5) → False)))) := by
  intro assump_1
  intro assump_2
  intro assump_3
  intro assump_4
  cases assump_4
  case intro assump_5 assump_6 =>
    cases assump_3
    case intro assump_11 assump_12 =>
      cases assump_11
      case intro assump_13 assump_14 =>
        cases assump_12
        case intro assump_19 assump_20 =>
          cases assump_1
          case inl assump_27 =>
            have assump_53 : ((p1 ∧ p3) ∨ (p4 → p7)) := by
              apply Or.inl
              apply And.intro
              exact assump_19
              exact assump_5
            let assump_31 := assump_27 assump_53
            have assump_54 : (False → p3) := by
              intro assump_33
              apply False.elim assump_33
            let assump_32 := assump_31 assump_54
            apply False.elim assump_32
          case inr assump_28 =>
            cases assump_28
            case intro assump_39 assump_40 =>
              have assump_55 : (p6 ∨ p3) := by
                apply Or.inr
                exact assump_5
              let assump_49 := assump_39 assump_55
              apply False.elim assump_49


variable (p3 p1 p0 p2 p4 p7 p6 p5 : Prop)
theorem file75_143920 : (((((p4 ∨ p0) ∨ (False → False)) ∨ ((p0 ∨ True) → False)) ∨ (((p6 ∧ p5) ∨ (True ∧ p4)) → False)) ∨ ((((p6 ∧ p7) → (p3 ∨ False)) → ((p1 → p7) ∨ (False ∨ p4))) ∨ (((p3 → False) ∧ (False → p3)) → ((p2 → p6) → False)))) := by
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Or.inr
  intro assump_12
  apply False.elim assump_12


variable (p1 p3 p2 p5 : Prop)
theorem file75_144303 : ((((((p5 → p1) → (p2 ∧ p1)) → ((p5 → p5) ∨ (p2 ∧ p1))) ∨ (((p2 ∧ p5) ∨ (True ∧ True)) ∨ ((False → p1) → (p3 → p3)))) → False) → False) := by
  intro assump_1
  have assump_14 : ((((p5 → p1) → (p2 ∧ p1)) → ((p5 → p5) ∨ (p2 ∧ p1))) ∨ (((p2 ∧ p5) ∨ (True ∧ True)) ∨ ((False → p1) → (p3 → p3)))) := by
    apply Or.inl
    intro assump_5
    apply Or.inl
    intro assump_8
    exact assump_8
  let assump_4 := assump_1 assump_14
  apply False.elim assump_4


