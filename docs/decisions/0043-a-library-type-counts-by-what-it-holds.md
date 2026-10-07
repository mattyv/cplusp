# 0043: A library type counts by what it holds

Date: 2026-10-07. Status: decided. Amends 0041, whose test counted a library template by its type arguments alone in the build.

## Decision

The test of decision 0041, whether a value carries a way to write, reads what a type holds.

- **Any record, of the file or of the library,** carries what its fields and bases carry. A template of the library also carries what its type arguments carry. So a view, a proxy, an insert iterator and a type-erased box carry a way to write when they hold a pointer to non-const.
- **A container that owns its elements on the heap** counts by its element types alone. These are `basic_string`, `vector`, `deque`, `list`, `forward_list`, and the ordered and unordered maps and sets. A copy of one copies the elements, so its own pointers are no second name for anything.
- **Const reaches the fields.** A const record carries what its fields carry as const. So a const node that holds `unique_ptr` members carries nothing, as decision 0042 says of a const `unique_ptr`. A pointer member of a const record still carries, because const does not reach its pointee.
- **A type the check cannot see whole carries a way to write.** An incomplete type is one. An analysis that cannot finish refuses, decision 0036.
- **The library is a place.** A test of the library asks where a declaration is, not which namespace holds it.

## Why

The build of 0041 counted a library template by its type arguments only, and a library class that is no template not at all. A sixth review of the green step of 0038 found four. `std::ranges::ref_view`, the proxy references of `vector<bool>` and `bitset`, and `std::any` each hold a pointer, whatever their arguments say. A list of such types by name would be one more list to outgrow. Reading what a type holds needs no list, except the few containers that own what they point to.

## What changes

The const-handle check reads fields and bases for every record, with the record's const, and the type arguments of a library template. It keeps a short list of owning containers. A test with the four library types, a copy of an owning container that stays clean, and a const holder of `unique_ptr` members that stays clean.
