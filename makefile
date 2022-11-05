doc:
	RUSTDOCFLAGS="--html-in-header doc/katex-header.html" cargo doc --no-deps

.PHONY: doc

# use the --tag-prefix "" to avoid a separate tag for each crate
# use the --dependent-version to avoid bumping each crate's dependencies, e.g. from `0.4.0-alpha` to `0.4.0-alpha.3`, 
# which would break due to circular dev-dependencies

# Since the master branch is protected, the current workflow is to create a release branch, e.g. `release-0.4` from `master`,
# commit the new version changes, and once the release is done, merge the release branch back to master.
release:
	cargo update
	cargo release alpha --dependent-version fix --tag-prefix "" --execute --allow-branch "release*"
