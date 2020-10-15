pub trait IteratorExt: Iterator {
    fn exactly_one(mut self) -> Option<Self::Item>
        where Self: Sized
    {
        let r = self.next();
        if r.is_some() && self.next().is_none() {
            r
        } else {
            None
        }
    }
}

impl<T: Iterator> IteratorExt for T {}