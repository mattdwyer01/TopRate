-- supabase_schema.sql
-- TopRate Supabase schema. Keep this in the repo as the authoritative record
-- of the database structure - the free tier has NO backups, so if the project
-- is ever lost, running this recreates the tables, then the load scripts
-- repopulate them from the CSVs.
--
-- Table: wpr_form_history
--   One row per (run_id, date): each run_id is a horse's form-capture event
--   that dumps one row per historical race date. Composite primary key on
--   (run_id, date). Loaded from wpr_form_history.csv.gz via
--   load_form_history_to_supabase.py (upsert on the composite key).

create table if not exists wpr_form_history (
  run_id            bigint,
  horse_id          bigint,
  horse             text,
  scrape_date       text,
  formnumber        integer,
  racenumber        integer,
  date              text,
  track             text,
  trackcode         text,
  trackgrading      double precision,
  distance          integer,
  going             text,
  wpr               double precision,
  weightcarried     double precision,
  barrier           integer,
  pricestarting     double precision,
  positionsettled   double precision,
  position800m      double precision,
  position600m      double precision,
  position400m      double precision,
  position200m      double precision,
  positionfinish    double precision,
  margin800m        double precision,
  margin600m        double precision,
  margin400m        double precision,
  margin200m        double precision,
  marginfinish      double precision,
  raceshapeearly    double precision,
  raceshapemid      double precision,
  raceshapelate     double precision,
  winner            text,
  isbarriertrial    boolean,
  sect_i_time       double precision,
  sect_ld_early     double precision,
  sect_i_early      double precision,
  sect_i_to600      double precision,
  sect_i_to800      double precision,
  sect_i_l200       double precision,
  sect_i_l400       double precision,
  sect_i_l600       double precision,
  sect_i_l800       double precision,
  sect_i_400_200    double precision,
  sect_i_600_400    double precision,
  sect_i_800_400    double precision,
  sect_i_800_600    double precision,
  field_size        double precision,
  weight_handicap   double precision,
  race_class        text,
  is_letup          boolean,
  is_spell          boolean,
  race_id           double precision,
  meeting_id        double precision,
  blinkers_on       boolean,
  gear_changes      text,
  comments_steward  text,
  comments_video    text,
  time_last600m     double precision,
  jockey            text,
  trainer           text,
  is_jumpout        boolean,
  primary key (run_id, date)
);

-- Helpful indexes for the queries the dashboard / analysis will run.
-- (Add these once; they speed up date-range and per-horse lookups.)
create index if not exists idx_wfh_date     on wpr_form_history (date);
create index if not exists idx_wfh_horse_id on wpr_form_history (horse_id);
create index if not exists idx_wfh_race_id  on wpr_form_history (race_id);

-- The dashboard's full-history fetch (lib/supabaseFormHistory.ts) filters on
-- horse=ilike.<name> (no stable horse_id in the JSON payload to key on
-- instead - see that file). A plain btree index on `horse` doesn't help an
-- ILIKE query (case-insensitive, and Postgres can't use a plain index for
-- that without citext), so once the table grew past ~400k rows this started
-- hitting the statement timeout as a sequential scan (Postgres error 57014,
-- found Aug 2026 debugging "only shows last 10 runs"). A trigram GIN index
-- is the standard fix for ILIKE lookups regardless of row count.
create extension if not exists pg_trgm;
create index if not exists idx_wfh_horse_trgm on wpr_form_history using gin (horse gin_trgm_ops);


-- ============================================================
-- Table: toprate_runners
--   One row per runner per race (run_id is unique). Loaded from
--   toprate_runners.csv via load_runners_to_supabase.py (upsert on run_id).
-- ============================================================

create table if not exists toprate_runners (
  date                  text,
  venue                 text,
  state                 text,
  race                  double precision,
  race_id               bigint,
  race_name             text,
  distance              double precision,
  prize_money           double precision,
  going                 text,
  track_grading         double precision,
  rail_position         text,
  start_time            text,
  race_class            text,
  race_shape_early      text,
  race_shape_mid        text,
  race_shape_late       text,
  has_first_starter     boolean,
  run_id                bigint primary key,
  tab_number            double precision,
  barrier               double precision,
  horse                 text,
  jockey                text,
  trainer               text,
  runs_with_wpr         double precision,
  wpr_nett              double precision,
  wpr_rank              double precision,
  wpr_last1             double precision,
  wpr_avg_last3         double precision,
  wpr_trend             double precision,
  wpr_consistency       double precision,
  wpr_peak_rank_1yr     double precision,
  wpr_dist              double precision,
  wpr_going             double precision,
  avg_settled_pos       double precision,
  avg_800m_pos          double precision,
  avg_400m_pos          double precision,
  early_speed_score     double precision,
  mid_speed_score       double precision,
  late_speed_score      double precision,
  total_speed_score     double precision,
  toprate_rating        double precision,
  toprate_price         double precision,
  speed_rating          double precision,
  pfm_score             double precision,
  pfm_score_rank        double precision,
  fixed_win_price       double precision,
  open_price            double precision,
  jockey_win_pct_90d    double precision,
  trainer_win_pct_365d  double precision,
  jockey_rating         double precision,
  trainer_rating        double precision,
  jt_combo_win_pct      double precision,
  jt_combo_rides        double precision,
  weight_trend          double precision,
  wins_at_dist          double precision,
  starts_at_dist        double precision,
  places_at_dist        double precision,
  going_breakdown       text,
  form_string           text,
  weight_carried        text,
  starting_price_sp     double precision,
  price_top             double precision,
  finish_position       double precision,
  margin_finish         double precision,
  won                   double precision,
  placed                double precision,
  resulted              double precision,
  wpr_actual            double precision,
  comments_video        text,
  comments_steward      text,
  -- Punting Form (pf_*) - the PF subscription was cancelled and the model
  -- runs on WPR projection only, but the CSV still carries these columns
  -- from before that removal, so the table needs them too or every upsert
  -- fails outright (see the Aug 2026 sync-outage note below).
  pf_ai_rank            double precision,
  pf_ai_price           double precision,
  pf_ai_score           double precision,
  pf_class_rank         double precision,
  pf_tac_class_rank     double precision,
  pf_time_rank          double precision,
  pf_early_time_rank    double precision,
  pf_last600_rank       double precision,
  pf_last400_rank       double precision,
  pf_last200_rank       double precision,
  pf_run_style          text,
  pf_class_change       double precision,
  pf_reliable           boolean,
  wpr_dist_n            double precision,
  sect_early            text,
  speed_rank_in_race    double precision,
  pace_scenario         text,
  contested_pace        boolean,
  _settling             text,
  wprp_proj             double precision,
  wprp_conf             double precision,
  wprp_price            double precision,
  wprp_rank             double precision,
  wprp_peak             double precision,
  wprp_desc             text,
  wprp_proj_alt         double precision,
  wprp_conf_alt         double precision,
  -- Market-blend / edge fields (Sep 2026 WPR-vs-market work).
  wprp_blend_price      double precision,
  wprp_blend_prob       double precision,
  wprp_blend_rank       double precision,
  wprp_edge             double precision,
  wprp_edge_mkt_prob    double precision,
  wprp_edge_prob        double precision,
  rs_score              double precision,
  rs_label              text,
  wpr_actual_rank       double precision,
  silk_url              text,
  -- Base/adjustment decomposition (wpr_projection.py's _compute_base() /
  -- ADJ_TERMS) and the miss-explanation fields (compute_miss_explanations()).
  wprp_base             double precision,
  wprp_adj              double precision,
  wprp_contrib          text,
  wprp_miss_category    text,
  wprp_miss_reason      text,
  -- Late scratch flag, set post-capture by toprate_price_refresh.py.
  scratched             double precision
);

create index if not exists idx_tr_date    on toprate_runners (date);
create index if not exists idx_tr_race_id on toprate_runners (race_id);
create index if not exists idx_tr_resulted on toprate_runners (resulted);

-- ============================================================
-- Public read access to wpr_form_history (Aug 2026, user request).
--
-- The dashboard frontend (frontend/src/lib/supabaseFormHistory.ts) queries
-- this table DIRECTLY from the browser using Supabase's public anon key -
-- so a horse's full career history can be shown in the Recent Runs table
-- without embedding it in toprate_data.json (which has to stay under
-- GitHub's 100MB push limit - see git history for the size testing that
-- ruled out embedding full history there once the race window was widened
-- back to 30 days).
--
-- The anon key is meant to be public (it's baked into the built
-- toprate_live.html); everything else that keeps this table safe is this
-- RLS policy. It only grants SELECT (read), only to the anon role, only on
-- this one table - the anon key can still do nothing else (no INSERT/
-- UPDATE/DELETE anywhere, no access to toprate_runners, which is left
-- locked down since it isn't queried client-side). Writes still only ever
-- happen server-side via supabase_sync.py's service_role key, which
-- bypasses RLS entirely and must never be exposed client-side.
--
-- Idempotent - safe to run again if RLS/the policy already exist.
alter table wpr_form_history enable row level security;

drop policy if exists "Public read access" on wpr_form_history;
create policy "Public read access"
  on wpr_form_history
  for select
  to anon
  using (true);

-- ============================================================
-- Migration (Aug 2026): toprate_runners had drifted 20 columns behind
-- toprate_runners.csv - CREATE TABLE IF NOT EXISTS above is a no-op on an
-- existing table, so the columns above never actually reached the live
-- database. PostgREST rejects an upsert containing ANY unknown column for
-- the WHOLE request, and supabase_sync.py's _upsert() aborts entirely on
-- the first failed batch - so the daily sync had been failing at row 0 on
-- every run (confirmed via Action logs: "Could not find the 'open_price'
-- column"), and toprate_runners had been frozen at whatever the last fully-
-- successful sync captured. Run this once against the live database to
-- catch it up; safe to re-run (ADD COLUMN IF NOT EXISTS).
-- ============================================================
alter table toprate_runners add column if not exists open_price         double precision;
alter table toprate_runners add column if not exists pf_ai_rank         double precision;
alter table toprate_runners add column if not exists pf_ai_price        double precision;
alter table toprate_runners add column if not exists pf_ai_score        double precision;
alter table toprate_runners add column if not exists pf_class_rank      double precision;
alter table toprate_runners add column if not exists pf_tac_class_rank  double precision;
alter table toprate_runners add column if not exists pf_time_rank       double precision;
alter table toprate_runners add column if not exists pf_early_time_rank double precision;
alter table toprate_runners add column if not exists pf_last600_rank    double precision;
alter table toprate_runners add column if not exists pf_last400_rank    double precision;
alter table toprate_runners add column if not exists pf_last200_rank    double precision;
alter table toprate_runners add column if not exists pf_run_style       text;
alter table toprate_runners add column if not exists pf_class_change    double precision;
alter table toprate_runners add column if not exists pf_reliable        boolean;
alter table toprate_runners add column if not exists wprp_base          double precision;
alter table toprate_runners add column if not exists wprp_adj           double precision;
alter table toprate_runners add column if not exists wprp_contrib       text;
alter table toprate_runners add column if not exists wprp_miss_category text;
alter table toprate_runners add column if not exists wprp_miss_reason   text;
alter table toprate_runners add column if not exists scratched          double precision;

-- ============================================================
-- Migration (Sep 2026, round 2): the migration above was generated by
-- diffing the CSV against THIS FILE, not the live database - and it turns
-- out this file had already drifted from the live table independently
-- (pfm_score/pfm_score_rank were declared in the CREATE TABLE block above
-- for a while, but the matching ALTER TABLE was apparently never actually
-- run against the live database). This round was instead generated from
-- `select string_agg(column_name, ', ' order by column_name) from
-- information_schema.columns where table_name = 'toprate_runners'` run
-- directly against the live database, so it's a true fix rather than
-- another guess from a possibly-stale proxy. Also picks up
-- wprp_blend_*/wprp_edge_* - new columns from unrelated WPR work that
-- landed on main between the round-1 migration and this one.
-- ============================================================
alter table toprate_runners add column if not exists pfm_score          double precision;
alter table toprate_runners add column if not exists pfm_score_rank     double precision;
alter table toprate_runners add column if not exists wprp_blend_price   double precision;
alter table toprate_runners add column if not exists wprp_blend_prob    double precision;
alter table toprate_runners add column if not exists wprp_blend_rank    double precision;
alter table toprate_runners add column if not exists wprp_edge          double precision;
alter table toprate_runners add column if not exists wprp_edge_mkt_prob double precision;
alter table toprate_runners add column if not exists wprp_edge_prob     double precision;
