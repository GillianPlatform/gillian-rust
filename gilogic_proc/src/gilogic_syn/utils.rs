use syn::{
    spanned::Spanned,
    visit_mut::{self, VisitMut},
    Path, PathSegment, QSelf, Token, Type, TypePath,
};

pub(super) struct SelfReplacer<'a> {
    pub replace_with_ty: Type,
    pub trait_name: &'a Path,
}

impl<'a> VisitMut for SelfReplacer<'a> {
    fn visit_type_path_mut(&mut self, ty_path: &mut TypePath) {
        visit_mut::visit_type_path_mut(self, ty_path);
        if ty_path.qself.is_none()
            && ty_path.path.leading_colon.is_none()
            && matches!(ty_path.path.segments.iter().next(), Some(PathSegment { ident, arguments }) if &ident.to_string() == "Self" && arguments.is_empty())
        {
            let segments = std::mem::take(&mut ty_path.path.segments);
            let q = QSelf {
                lt_token: Token![<](ty_path.span()),
                ty: Box::new(self.replace_with_ty.clone()),
                position: self.trait_name.segments.len(),
                as_token: Some(Token![as](ty_path.span())),
                gt_token: Token![>](ty_path.span()),
            };
            ty_path.qself = Some(q);
            ty_path.path.leading_colon = self.trait_name.leading_colon;
            let mut new_segments = self.trait_name.segments.clone();
            for rest in segments.into_iter().skip(1) {
                new_segments.push(rest);
            }
            ty_path.path.segments = new_segments;
        }
    }
}
