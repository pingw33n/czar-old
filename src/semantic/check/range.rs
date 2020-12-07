use super::*;
use super::lang::RangeItem;

impl PassImpl<'_> {
    pub fn check_range(&mut self, node: NodeId /*Range*/) -> Result<TypeId> {
        let &Range { kind, start, end } = self.hir.range(node);
        let start = if let Some(n) = start {
            Some(self.typing(n)?)
        } else {
            None
        };
        let end = if let Some(n) = end {
            Some(self.typing(n)?)
        } else {
            None
        };
        let args = match (start, end) {
            (Some(s), Some(e)) => {
                self.unify(s, e);
                let s = self.normalize(s);
                let e = self.normalize(e);
                if s != e {
                    self.error(node, format!(
                        "mismatching types in range literal: start bound is `{}`, end bound is `{}`",
                        self.display_type(s),
                        self.display_type(e)));
                }
                vec![s]
            }
            (Some(ty), None) | (None, Some(ty)) => vec![ty],
            (None, None) => vec![],
        };
        let lang_item = match (start, end) {
            (Some(_), Some(_)) => match kind {
                RangeKind::Exclusive => RangeItem::Range,
                RangeKind::Inclusive => RangeItem::RangeInclusive,
            }
            (Some(_), None) => RangeItem::RangeFrom,
            (None, Some(_)) => match kind {
                RangeKind::Exclusive => RangeItem::RangeTo,
                RangeKind::Inclusive => RangeItem::RangeToInclusive,
            }
            (None, None) => RangeItem::RangeFull,
        };
        let ty = self.std().type_(LangItem::Range(lang_item));
        Ok(self.insert_type((self.package_id, node), TypeData::Instance(TypeInstance {
            ty,
            args,
        })))
    }
}