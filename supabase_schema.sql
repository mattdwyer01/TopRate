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
  fixed_win_price       double precision,
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
  rs_score              double precision,
  rs_label              text,
  wpr_actual_rank       double precision,
  silk_url              text
);

create index if not exists idx_tr_date    on toprate_runners (date);
create index if not exists idx_tr_race_id on toprate_runners (race_id);
create index if not exists idx_tr_resulted on toprate_runners (resulted);
