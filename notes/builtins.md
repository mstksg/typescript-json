Supporting Typescript Built-In Utility Types
============================================

Partial
-------

Verdict: **Full Support**

Works as expected pretty much; however, you really can't be too fine-grained
with using the new type on the Haskell side.  That's because all of the fields
are "mixed together" to create the `a` in `TSType p k a`.  So the resulting
`TSType p k (Maybe a)` will have all of the required fields as either all
present, or all non-present: you can't really hook into the details of the
encoder/decoder.

Required
--------

Verdict: **No Support: Encoding Issue**

Not supportable.  That's because in the `TSType p k a`, the `a` might not
*contain* something from all of the fields.  This causes problems when
*encoding*: the encoding will potentially encode an `a` into some fields as
`Nothing`, but this cannot be encoded into a record with all fields
required.  The best we could do is turn optional fields into required fields
unioned with `null`, but that kind of defeats the purpose of this.

Read Only
---------

Verdict: **Possible, Benefit in question**

Not provided only because all objects are sort of implied read-only anyway.
Should we add the ability to add this annotation?  It's more or less
meaningless on the haskell & json side.

Record
------

Pick
----

Verdict: **Haskell-Side Support (Decoding Issue)**

Apparently not supportable because of the *decoding* aspect: to decode into an
`a` we need to feed it something from every field.  Can't really do this then
without providing "default values" for every omitted field.  At that point,
might as well use `Omit`.

Hm, we can maybe actually sort of simulate this if we only ever omit optional
fields. And we can force this too by requiring them to Partial things first.
Ah!  This might work!

Omit
----

Verdict: **Haskell-Side Support (Decoding Issue)**

Should be technically possible, but unclear if useful.  That's because we
essentially need to provide default values for every omitted field during the
decoding process, but the types of those default values aren't checkable
really.  Unless it's in an existential with an Assign.

Ah, we could also only ever allow omitting optional fields, the same route as
Pick.

Exclude
-------

Verdict: **Haskell-Side Support (Encoding Issue)**

Perhaps not supportable for the same reason as `Required`.  We would need to be
able to encode an `a` when it was created with one of the excluded
constructors.

One possible as a non-builtin but custom combinator is to "collapse" all of the
omitted possibilities to be null.

Extract
-------

Verdict: **Haskell-Side Support (Encoding issue)**

Similar problem with `Exclude` presumably.  Encoding is the issue.

One possible as a non-builtin but custom combinator is to "collapse" all of the
omitted possibilities to be null.

NonNullable
-----------

Verdict: **Haskell-Side Support (Encoding issue)**

Definitely same issue as `Exclude`/`Extract`.  Not possible to get the same
behavior, but we can imitate it with a custom combinator.

Function-based
--------------

Verdict: **Meaningless**

`Parameters`, `ConstructorParameters`, `ReturnType`, `ThisParameterType`,
`OmitThisParameter`, `ThisType` all seem to only make sense in the context of
functions, which are not supported.

String-Based
------------

Verdict: **Possible**

Should be straightforward, but need to use the extends/assignability system.
